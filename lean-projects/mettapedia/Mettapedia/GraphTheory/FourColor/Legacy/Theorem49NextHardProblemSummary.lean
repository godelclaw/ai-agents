import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49DerivationImpossibilitySummary
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometry
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusWitnessRegression
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestGeometryRegression
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceCanonicalWitness
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacement
import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryFreeSelectorPositiveRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacementRoute
import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49PositiveGeometricSourceReplacementJointObstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceConstruction
import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49PositiveGeometricSourceReplacementRegression

/-!
# Next hard problem for Theorem 4.9 route: Honest sources and previous-boundary witness

## Current status summary

### Completed work

1. **Spanning gap bridge** (completed 2026-04-29)
   - Geometric witness surfaces → BoundaryZeroAnnihilatorTrivial → Kempe generator spanning
   - Files: `Theorem49SpanningGap.lean`, `Theorem49KempeGeneratorSpan.lean`
   - Algebraic bottleneck resolved

2. **Impossibility results** (established)
   - Cyclic source ↛ at-most-one interior edge per face
     - Counterexample: shared-interior-pair witness
     - File: `Theorem49CyclicSourceAtMostOneDerivation.lean`
   - At-most-one + cyclic source ↛ nonempty carrier
     - Counterexample: chained-diamonds-with-triangle
     - File: `Theorem49AtMostOneNonemptyCarrierImpossibility.lean`
   - Boundary reachability + successor-cycle source + selected arcs + at-most-one
     ↛ nonempty carrier
     - Counterexample: diamond-with-triangle
     - File: `Theorem49AtMostOneNonemptyCarrierImpossibility.lean`
   - Stronger: successor-cycle facial dart data + facewise at-most-one forces the
     purified interior-edge endpoint carrier to be empty
     - Theorem: `selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_dartSuccessorCycleEmbeddingData_and_facewiseAtMostOneInteriorEdge`
     - File: `Theorem49AtMostOneNonemptyCarrierImpossibility.lean`
   - Strongest current form: honest facial closed-walk data + facewise at-most-one
     already forces the purified carrier to be empty
     - Theorem: `selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_of_closedWalkEmbeddingData_and_facewiseAtMostOneInteriorEdge`
     - File: `Theorem49AtMostOneNonemptyCarrierImpossibility.lean`
   - Necessary-condition form: an honest closed-walk annulus source with the live endpoint
     witness `HasUnblockedInteriorEndpoint` must have some face boundary carrying two
     distinct interior edges
     - Theorem: `exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint`
     - File: `Theorem49AtMostOneNonemptyCarrierImpossibility.lean`
   - Summary: `Theorem49DerivationImpossibilitySummary.lean`

3. **Collar geometry structure** (defined)
   - `PlanarBoundaryAnnulusCollarGeometry`: basic annulus geometry with witness edges
   - `PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry`: repaired version adding
     `hwitnessPrev` constraint
   - The constraint: witness edges of positive collars must lie on the previous boundary cycle
   - This is needed for well-founded parent-peeling

4. **Constructive positive source packages, obstruction, and replacement surface**
   (completed 2026-04-30)
   - `Theorem49BoundaryRootNonemptyProjectedSynthesis` packages non-vacuous theorem-4.9
     synthesis with the corrected projected Definition 4.8 subspace and family-span equalities
   - `Theorem49PositiveGeometricSource.lean` records the explicit geometric construction
     surfaces:
     closed-walk canonical choice, closed-walk same-boundary one-collar geometry, and their
     successor-cycle boundary-order versions
   - Each positive package lowers to the same nonempty projected synthesis endpoint for any
     supplied Tait coloring
   - `Theorem49PositiveGeometricSourceImpossibility.lean` proves that all four current package
     surfaces are inconsistent with the present purified nonempty carrier:
     `not_nonempty_currentTheorem49PositiveGeometricSourcePackages`
   - `Theorem49PositiveGeometricSourceReplacement.lean` records the direct replacement surfaces:
     `Theorem49HeightOrderedPositiveProjectedGeometry` and
     `Theorem49CollarLayerPositiveProjectedGeometry`
   - These replacement packages lower to `Theorem49BoundaryRootNonemptyProjectedSynthesis`
     without passing through canonical witness choice, and their fixed-embedding predicates are
     equivalent by converting height data to finite collars and finite collars back to heights
   - `Theorem49PlanarBoundaryPeeling.lean` now proves
     `PlanarBoundaryWellFoundedFacePeelWitnessData.toPlanarBoundaryHeightOrderedFacePeelWitnessData`
     and
     `admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_admitsPlanarBoundaryWellFoundedFacePeelWitnessData`;
     explicit well-founded parent-peeling data therefore feeds the direct height-ordered
     replacement surface through the canonical `parentHeight` rank, so an acyclic witness
     dependency is now a positive construction input rather than a separate endpoint
   - The same file now factors the wheel-style cycle blocker into generic witness-cover
     infrastructure: non-boundary remainder edges whose values are other peeled-face witnesses
     force parent/height dependencies, and injective witness choices make any nonempty finite
     closed remainder-witness chain impossible for both
     `PlanarBoundaryWellFoundedFacePeelWitnessData` and
     `PlanarBoundaryHeightOrderedFacePeelWitnessData`.  The generic list-level order lemma is
     `false_of_isChain_height_lt_and_getLast_lt_head`, and the wheel-with-inner-triangle
     height-cycle regression now closes its two concrete orientations by applying this list-level
     obstruction directly to the discovered three-face cycles.  The well-founded parent side now
     also has the direct parent-map finite-cycle obstruction
     `false_of_isChain_parentRel_and_getLast_parent_head`, so closed parent chains are blocked
     before repackaging them as height inequalities.
  - `Theorem49PositiveGeometricSourceReplacement.lean` now consumes that acyclic surface
     directly: well-founded parent witness-cover data plus `HasUnblockedInteriorEndpoint`
     constructs both the height-ordered and finite-collar replacement packages.  Those named
     positive packages now already expose full `Theorem49BoundaryRootSynthesis`, and the route
     file adds the closed-walk traceability theorem
     `theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint`
   - `PlanarBoundaryClosedWalkSourceRoute.lean` now exposes the fixed-embedding constructor
     `planarBoundaryWellFoundedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData`,
     so honest closed-walk source data plus generic boundary-root interior-dual
     adjacency-distance data yields the explicit acyclic witness-cover input on the same
     embedding; `Theorem49PositiveGeometricSourceReplacementRoute.lean` then reaches
     `Theorem49BoundaryRootNonemptyProjectedSynthesis` from that source/interior-dual package
     plus `HasUnblockedInteriorEndpoint`, with a matching successor-cycle source theorem
   - The root-distance source layer now also derives that endpoint witness from the older
     endpoint-separation surface or from peeled-face endpoint no-touch on the root-distance
     annulus construction: closed-walk and successor-cycle source fields plus raw
     `interiorEdgeEndpointSupport` nonemptiness and either global endpoint-support disjointness
     or root-distance peeled-face endpoint no-touch reach the same projected synthesis endpoint
  - The direct well-founded witness-cover lane now accepts the same endpoint-separation
     carrier surface without first packaging `HasUnblockedInteriorEndpoint`: explicit
     `PlanarBoundaryWellFoundedFacePeelWitnessData` plus raw
     `interiorEdgeEndpointSupport` nonemptiness and endpoint-support disjointness reaches
     height-ordered geometry, finite-collar geometry, and full theorem-4.9, with closed-walk
     and successor-cycle source-facing wrappers and matching well-founded graph-package
     `boundaryRootSynthesis` closures
   - `Theorem49InteriorVertices.lean` now proves that nonempty interior-edge support supplies
     that raw endpoint carrier, and the closed-walk root-distance source bridge has direct
     projected-synthesis variants with nonempty `interiorEdgeSupport` in place of pre-expanded
     raw endpoint nonemptiness
   - The same file now provides graph-level constructors and existential bridge theorems from
     annulus collar geometry, or repaired previous-boundary witness geometry, plus a surviving
     purified carrier; it now also exposes the direct projected-synthesis bridge from those
     minimal hypotheses via
     `exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_annulusCollarGeometry_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct`
   - The annulus-collar bridges now also accept the named local endpoint witness
     `HasUnblockedInteriorEndpoint`, with direct fixed-embedding, graph-level, nonempty-package,
     and projected-synthesis constructors, so callers no longer have to separately repackage
     the purified carrier when they can exhibit one unblocked interior endpoint
   - The older endpoint-separation surface now feeds that witness directly:
     `hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty` turns raw
     `interiorEdgeEndpointSupport` nonemptiness plus endpoint-support disjointness from the
     selected boundary into `HasUnblockedInteriorEndpoint`; the annulus-collar replacement and
     route files expose matching direct projected-synthesis wrappers for the closed-walk and
     successor-cycle source shells
   - The route-facing closed-walk and successor-cycle annulus-collar package constructors now
     also accept this raw endpoint-support-separated input directly, so downstream callers can
     choose either the named local endpoint witness or the older endpoint-separation surface
     without changing the package they inhabit
   - Peeled-face endpoint no-touch now also reaches the annulus-collar replacement packages
     through the canonical collar-to-construction lowering:
     `PlanarBoundaryAnnulusCollarGeometry.hasUnblockedInteriorEndpoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport`
     turns no-touch on
     `planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data` plus raw
     `interiorEdgeEndpointSupport` nonemptiness into `HasUnblockedInteriorEndpoint`, and
     `Theorem49PositiveGeometricSourceReplacement.lean` exposes direct finite-collar,
     height-ordered, and projected-synthesis constructors from that surface
   - `Theorem49PositiveGeometricSourceReplacementRoute.lean` now exposes the same
     peeled-face no-touch surface at the honest source layer: closed-walk and successor-cycle
     source data plus same-embedding annulus collar geometry, canonical peeled-face endpoint
     no-touch, and raw `interiorEdgeEndpointSupport` nonemptiness directly inhabit the
     route-facing annulus-collar positive packages and reach the nonempty projected synthesis
     endpoint
   - The same source-layer peeled-face no-touch inputs now also directly inhabit the
     graph-level finite-collar and height-ordered replacement packages, so callers no longer
     need to first package a route-facing annulus-collar source and then lower it separately
   - `Theorem49PlanarBoundaryAnnulusGeometry.lean` now proves the fixed-embedding
     honest-source cardinal route:
     `exists_oneCollarAnnulusCollarGeometry_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge`
     constructs a source-preserving one-collar annulus collar geometry from an honest
     closed-walk source plus only the facewise cardinal at-most-one interior-edge bound; the
     source supplies fallback edges and the annulus boundary split supplies the non-interior
     boundary-rest clause
   - The same file now exposes the graph-level version
     `exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdgeCardinality`,
     so the geometric construction endpoint can be invoked directly from an existential
     honest closed-walk annulus source plus the facewise cardinal bound, preserving the
     source boundary split on the chosen embedding
   - The canonical facewise witness route now also lands directly on the repaired
     previous-boundary witness surface:
     `PlanarBoundaryCanonicalWitnessChoice.toPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry`
     builds the repaired geometry from the canonical choice itself, and
     `exists_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice`
     exposes the honest-source existential form.  This uses the source-built one-collar
     geometry, where the positive-collar witness obligation is vacuous; arbitrary supplied
     weak collars remain governed by the explicit `WitnessOnCurrentBoundary` condition.
   - `Theorem49PositiveGeometricSourceReplacementRoute.lean` now connects this replacement
     surface back to both the honest closed-walk annulus source shell and the successor-cycle
     boundary-order source shell without reintroducing canonical choice or one-collar
     hypotheses: source data plus same-embedding annulus collar geometry and either nonempty
     purified carrier or `HasUnblockedInteriorEndpoint` yields the replacement graph packages and
     directly reaches the nonempty projected synthesis endpoint
   - The repaired previous-boundary witness lane now consumes the same endpoint witness directly:
     `theorem49CollarLayerPositiveProjectedGeometryOn_of_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint`,
     `theorem49HeightOrderedPositiveProjectedGeometryOn_of_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint`,
     and
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint`
     feed the direct replacement predicates and projected endpoint without first unpacking a
     purified-carrier proof.  The route file adds the closed-walk traceability theorem
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint`
     for source-facing positive constructions.
   - `Theorem49InteriorVertices.lean` now exposes the carrier nonemptiness obligation in
     named witness form:
     `HasUnblockedInteriorEndpoint`, equivalent to
     `selectedBoundaryInteriorEdgeEndpointVertices` being nonempty by
     `hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty`.
     The constructive burden is therefore an interior face-incidence edge with one endpoint
     avoiding every selected ambient-boundary edge
   - `Theorem49PositiveGeometricSourceConstruction.lean` proves the first inhabited positive
     replacement benchmark: the two-collar annulus geometry has finite collar-layer and
     height-ordered witness data together with nonempty purified selected-boundary carrier, and
     an explicit constant nonzero Tait coloring pushes this concrete geometry through the
     minimal annulus-collar/carrier bridge to
     `Theorem49BoundaryRootNonemptyProjectedSynthesis`
   - The same benchmark now has the concrete raw theorem-4.9 quotient package
     `counterEmbedding_collarGeometry_explicitTait_nonemptyCarrier_to_theorem49RawQuotientErrorPackage`,
     bundling actual collar geometry, explicit Tait coloring, nonempty purified carrier,
     nonempty projected synthesis, and the raw Definition 4.8 representative plus
     selected-boundary-kernel error decomposition for every Kirchhoff chain on that embedding
   - The same benchmark now computes its carrier geometry exactly:
     `counterEmbedding_interiorEdgeSupport_eq`,
     `counterEmbedding_interiorEdgeEndpointSupport_eq`,
     `counterEmbedding_selectedBoundaryEndpointSupport_eq`, and
     `counterEmbedding_endpointSupport_disjoint_selectedBoundarySupport` show that the shared
     intermediate edge supplies a raw endpoint carrier disjoint from selected-boundary endpoints,
     yielding the named witness `counterEmbedding_hasUnblockedInteriorEndpoint`
   - The same construction now calibrates the repaired previous-boundary route directly:
     `counterEmbedding_previousBoundaryWitness_nonemptyProjectedSynthesis_without_parentWitnessOrientation`
     combines `counterPreviousBoundaryWitnessGeometry`, the endpoint witness, and the nonempty
     projected synthesis endpoint while still refuting the stricter canonical annulus
     construction `ParentWitnessOrientation` condition on the same collar
   - `Theorem49PositiveGeometricSourceReplacementRegression.lean` proves that the honest
     shared-interior-pair annulus still fails both direct replacement predicates despite carrying
     boundary reachability, successor-cycle selected arcs, a Tait coloring, and nonempty purified
     selected-boundary carrier; the same regression now also refutes the route-facing
     closed-walk and successor-cycle annulus-collar packages on that embedding.  The obstruction
     has also been strengthened to the explicit local endpoint witness
     `HasUnblockedInteriorEndpoint`: even that first-order carrier witness, with the same
     source and coloring data, does not force any direct or route-facing replacement package.
     The strengthened closed-walk-source form
     `not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
     now shows the same failure from an honest closed-walk annulus boundary source itself,
     a Tait coloring, and the explicit endpoint witness.  The companion theorem
     `not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
     shows that even adding exact one-collar source-preserving current-boundary data still does
     not force any direct or route-facing replacement package; the successor-cycle analogue
     `not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
     records the same failure on the boundary-order shell.
     The companion theorem
     `not_forall_some_witnessCoverData_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
     lowers the obstruction one layer further: these source, coloring, and endpoint hypotheses
     also do not force either raw height-ordered or collar-layer witness-cover datum.  The
     bundled obstruction
     `not_forall_some_currentSufficientSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
     rules out all current sufficient same-embedding geometric endpoints from those hypotheses:
     height-ordered data, collar-layer data, the attached certificate, well-founded witness data,
     and annulus-collar geometry
   - `Theorem49PlanarBoundaryAnnulusWheelWitnessRegression.lean` now strengthens the wheel
     benchmark from a canonical/one-collar obstruction to a raw witness-cover obstruction:
     `not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle`
     proves that the three interior spokes force a strict height cycle around the wheel faces,
     and
     `not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle`
     transfers the obstruction to finite collar-layer data.  The same height-cycle also blocks
     the well-founded parent-peeling surface by
     `not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle`, because
     well-founded parent data now lowers to canonical parent-height data, and it blocks
     weak annulus-collar geometry by
     `not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle`, since every such
     collar lowers to height-ordered witness-cover data.  The failed universal
     `not_forall_some_acyclicWitnessCover_or_annulusCollarGeometry_of_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`
     records the route consequence: Tait colorability plus nonempty purified carrier still does
     not construct any current acyclic witness-cover or weak annulus-collar same-embedding
     geometry when the interior-face dependency graph has an unbroken cycle
   - That obstruction is now available without mentioning the wheel model: the generic
     well-founded and height-ordered finite-cycle lemmas in
     `Theorem49PlanarBoundaryPeeling.lean` turn any injective non-boundary
     remainder-witness dependency cycle into a contradiction.  Future source-to-witness
     derivations must therefore prove a selected-boundary break, a witness identification that
     collapses the apparent cycle, or an honest well-founded orientation.
   - The same wheel embedding now also carries an explicit honest closed-walk annulus boundary
     source via `wheelWithInnerTriangleClosedWalkAnnulusBoundarySource`, and the source-bearing
     failed universal
     `not_forall_some_acyclicWitnessCover_or_annulusCollarGeometry_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`
     shows that honest closed-walk source data, Tait colorability, and nonempty purified carrier
     still do not force any of the current acyclic witness-cover or weak annulus-collar endpoints
   - The same strict height-cycle now also blocks the direct positive replacement packages and
     the repaired previous-boundary witness surface on that source-bearing wheel embedding:
     `not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle`,
     `not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle`, and
     `not_forall_some_replacementPositiveProjectedGeometry_or_previousBoundaryWitness_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`
     show that the live positive endpoints require a genuine cycle-breaking geometric input,
     not just honest source data, Tait colorability, and the purified carrier
   - The same wheel benchmark now blocks the natural residual/current-boundary repair surface
     explicitly too:
     `not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_wheelWithInnerTriangle` and
     `not_forall_theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`
     show that the residual wrapper does not escape the same three-spoke obstruction either

### Known obstructions

1. **Basic collar geometry does not force previous-boundary witness**
   - File: `Theorem49PlanarBoundaryAnnulusWitnessRegression.lean`
   - Counterexample: `counterCollarGeometry` satisfies all collar geometry axioms but violates
     previous-boundary witness property on middle collar face
   - Theorem: `not_forall_previousBoundaryWitness_counterCollarGeometry`

2. **Honest sources CAN satisfy previous-boundary witness**
   - File: `Theorem49PlanarBoundaryAnnulusHonestGeometryRegression.lean`
   - Positive example: `diamondWithTriangle` honest source satisfies previous-boundary witness
   - Witness: `diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry`
   - But this is a specific model, not a universal derivation

## The next hard problem

**Question:** How can one construct one of the direct replacement positive packages from natural
boundary-order geometry while preserving a nonempty purified selected-boundary carrier?

The older question, "do honest closed-walk sources force previous-boundary witness geometry?",
has split into checked negative and positive cases.  Honest source data alone is refuted by the
shared-interior-pair model.  Honest source plus an arbitrary same-embedding weak collar is also
refuted by the connected chained-diamonds two-collar model.  The narrower source-tied
canonical-choice and one-collar packages have now been refuted as non-vacuous targets too:
canonical witness choice gives facewise at-most-one, and one-collar geometry gives canonical
witness choice.  Together with the closed-walk at-most-one obstruction, all four current
positive package surfaces force the purified carrier empty.  The facewise
at-most-one/nonempty-carrier branch is therefore not a live positive target, and neither are the
canonical-choice or one-collar nonempty-carrier packages unless the carrier definition or source
surface changes.  Equivalently, any honest closed-walk annulus source with the current local
unblocked endpoint witness must intentionally contain a face with two distinct interior edges,
which directly forbids canonical witness choice and source-preserving one-collar geometry on that
same source boundary split.  By contrast, the bare source-preserving
`PlanarBoundaryAnnulusCurrentBoundaryData` shell is no longer part of the obstruction picture:
`planarBoundaryAnnulusDecomposition_of_boundaryData` and
`PlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusCurrentBoundaryData` already produce a
one-collar current-boundary package from any honest annulus source boundary split, and the new
theorems `exists_oneCollarAnnulusCurrentBoundaryData_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource`,
`exists_oneCollarAnnulusCurrentBoundaryData_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc`,
`closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData`,
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData`
show that the shared-interior-pair benchmark positively inhabits that weak shell.  What still
fails there are the stronger exact-count repairs
`not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_two_sharedInteriorPair`,
`not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_three_sharedInteriorPair`,
and their successor-cycle analogues.  More sharply, the route-facing theorem
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_without_currentSufficientSameEmbeddingGeometry_sharedInteriorPair`
shows that even the honest closed-walk source package, after adding exact one-collar
current-boundary data together with a real Tait coloring and nonempty purified carrier, still
does not force any of the current sufficient same-embedding geometry surfaces on that benchmark.
The same exact one-collar obstruction survives even after replacing the raw carrier-nonempty
hypothesis by the named local endpoint witness `HasUnblockedInteriorEndpoint`: the theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_currentSufficientSameEmbeddingGeometry_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_currentSufficientSameEmbeddingGeometry_sharedInteriorPair`
show that even exact one-collar current-boundary data together with a real Tait coloring and an
explicit unblocked endpoint still do not force any current sufficient same-embedding geometry on
the shared-interior-pair benchmark.  Lean now isolates the smaller exact-shell failure too:
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_witnessCoverData_sharedInteriorPair`,
`not_forall_some_witnessCoverData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`,
and the successor-cycle analogues show that this exact one-collar endpoint-witness shell already
fails even raw height-ordered/collar-layer witness-cover data, before attached certificates,
well-founded witness data, or weak annulus-collar geometry enter.  More sharply, the replacement-regression theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair`
show that this strengthened exact one-collar shell still does not force even the direct or
route-facing replacement-positive packages.
The same failure persists on the boundary-order shell via
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_without_currentSufficientSameEmbeddingGeometry_sharedInteriorPair`
so the live theorem-4.9 construction burden begins strictly above naked current-boundary data,
and in practice above the exact one-collar current-boundary shell already at the honest-source
layer.  The construction-side burden is now explicit on the actual downstream shell:
`everyInteriorEdgeHasBoundaryFreeIncidentFace_of_planarBoundaryAnnulusConstructionFaceLayerData`,
`boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusConstructionFaceLayerData`, and
`not_nonempty_forcingInteriorEdgeWitness_of_planarBoundaryAnnulusConstructionFaceLayerData`
show that any sound v23.5 theorem reaching
`PlanarBoundaryAnnulusConstructionFaceLayerData` must already discharge the local
boundary-free-selector / no-forcing obligation; it cannot hide that burden in later annulus
decomposition wrappers.

### Why this matters

The `PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry` structure is required for:
- `PlanarBoundaryWellFoundedFacePeelWitnessData` (well-founded parent-peeling)
- `PlanarBoundaryHeightOrderedFacePeelWitnessData` (height-ordered witnesses)
- `PlanarBoundaryCollarLayerFacePeelWitnessData` (collar-layer witnesses)

These witness surfaces feed the spanning gap bridge to reach Kempe generator spanning.

Currently, the route must not assume that an arbitrary collar can be repaired from honest source
fields.  It also must not assume that canonical witness choice or source-preserving one-collar
geometry can coexist with the present nonempty purified carrier.  The immediate non-vacuous
projected endpoint is now the direct witness-data surface: construct height-ordered or finite
collar-layer witness-cover data on the same embedding as a nonempty purified carrier, then apply
`Theorem49PositiveGeometricSourceReplacement.lean`.
That same file now also proves
`theorem49BoundaryRootSynthesis_of_collarLayerPositiveProjectedGeometryOn`,
`Theorem49HeightOrderedPositiveProjectedGeometry.boundaryRootSynthesis`,
`Theorem49HeightOrderedPositiveProjectedGeometry.exists_boundaryRootSynthesis`,
and the matching collar-layer graph-package pair.  So once the route already reaches either of
those named positive witness-cover packages, full `Theorem49BoundaryRootSynthesis` is immediate;
the projected endpoint and raw quotient/error package are now explicit projections of that
stronger endpoint rather than the top of those surfaces.

The route-facing source bridges are now also present:
`Theorem49PositiveGeometricSourceReplacementRoute.lean` packages honest closed-walk annulus
source data, same-embedding annulus collar geometry, and nonempty purified carrier as
`Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometry`.  The same file packages the
successor-cycle boundary-order version as
`Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometry`, lowering it to the closed-walk
route package for traceability and to both replacement graph packages for the positive route.
Thus the live constructive target can be stated in source-facing terms without going back through
the refuted canonical-choice or same-boundary one-collar surfaces.  The shared-interior-pair
regression also now shows that the source-facing package still needs genuine annulus-collar or
witness-cover geometry: boundary reachability, successor-cycle selected arcs, Tait coloring, and
nonempty purified carrier do not force the closed-walk or successor-cycle annulus-collar package.
The same route file now also makes the facewise-at-most-one exclusion explicit at the package
level: `not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge`
and
`not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge`
show that neither route-facing annulus-collar positive package can ever serve as the positive
upgrade on the canonical at-most-one branch, and
`exists_two_distinct_interior_edges_on_faceBoundary_of_successorCycleAnnulusCollarPositiveProjectedGeometryOn`
exposes the same local two-interior-edge obstruction directly on the successor-cycle shell.
The stronger selected-boundary-contact construction shell is now blocked there too:
`not_theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge`
and
`not_theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge`
show that even this stronger source-facing package cannot inhabit the canonical at-most-one
branch, while
`exists_two_distinct_interior_edges_on_faceBoundary_of_successorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn`
exposes the same local two-interior-edge obstruction directly on the successor-cycle
selected-boundary-contact shell.
The stronger source-facing construction face-layer shell is now blocked the same way:
`not_theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge`
and
`not_theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn_of_facewiseAtMostOneInteriorEdge`
show that even this stronger annulus-decomposition-ready source package cannot sit on the
canonical at-most-one branch, while
`exists_two_distinct_interior_edges_on_faceBoundary_of_successorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn`
exposes the same local two-interior-edge obstruction directly on the successor-cycle
construction-face-layer shell.
For constructive use, those same graph-level annulus-collar packages now also expose
`boundaryRootSynthesis` and `exists_boundaryRootSynthesis`, so once the route reaches either
source-facing package, full `Theorem49BoundaryRootSynthesis` is already immediate and the older
projected-synthesis and raw quotient/error endpoints are only explicit projections.  The same
route file now also has direct closed-walk and successor-cycle full-synthesis theorems from
`HasUnblockedInteriorEndpoint`, together with the matching graph-level existential closures from
either a surviving carrier or a local endpoint witness, so the carrier side of future positive
source examples can be supplied by a local endpoint witness instead of an already packaged carrier
set.  The older endpoint-support-separation and canonical peeled-face no-touch criteria on
annulus-collar source data now factor through the same direct full-synthesis lane as well, so no
projected-synthesis-only remnant remains on that source surface.

The first concrete construction is now present:
`Theorem49PositiveGeometricSourceConstruction.lean` shows that the two-collar annulus benchmark
has a nonempty purified carrier, and combines that carrier with annulus collar geometry to inhabit
both direct replacement predicates and graph-level replacement packages.  The same file now gives
the benchmark a constant nonzero Tait coloring and proves
`counterEmbedding_boundaryRootNonemptyProjectedSynthesis`, so the concrete geometry reaches the
nonempty projected theorem-4.9 endpoint.  It now also proves the fixed-embedding raw endpoint
`counterEmbedding_collarGeometry_explicitTait_nonemptyCarrier_to_theorem49RawQuotientErrorPackage`,
so this positive benchmark is nonvacuous all the way to the raw Definition 4.8 quotient/error
package for every Kirchhoff chain.  The same benchmark is now also calibrated against the honest
source surface: `counterEmbedding_rawQuotientErrorPackage_without_closedWalkAnnulusBoundarySource`
bundles that raw endpoint with a proof that the same fixed embedding cannot carry an honest
closed-walk annulus source, because its graph is a three-edge matching.  This does not yet prove
a universal boundary-order theorem, but it establishes that the replacement surface is not
vacuous while preventing the benchmark from being mistaken for a source-side construction.  The
same file now also exposes that diagnosis at graph level:
`counterGraph_explicitTait_positiveProjectedGeometry_and_boundaryRootNonemptyProjectedSynthesis_without_closedWalkAnnulusBoundarySource`
packages the explicit Tait coloring, both graph-level direct replacement packages, a graph-level
nonempty projected theorem-4.9 endpoint, and failure of honest closed-walk annulus-source
admission for `counterGraph` itself.  So the current positive benchmark is now explicitly
classified as off the honest-source route already at graph level, not only on one chosen
embedding.  The stronger theorem
`counterGraph_explicitTait_positiveProjectedGeometry_and_boundaryRootNonemptyProjectedSynthesis_with_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData`
now shows that on the same fixed embedding the direct positive predicates and the projected
theorem-4.9 endpoint already coexist with a forcing interior edge and simultaneous failure of
`BoundaryFreeIncidentFaceSelector` and `PlanarBoundaryAnnulusConstructionFaceLayerData`.  So this
branch is not only off the honest-source route; even after the projected theorem-4.9 endpoint it
still does not supply the same-embedding selector/construction geometry needed by the present
positive route.  The
same file now also proves that the intermediate edge `em` is a concrete forcing interior edge on
that very benchmark:
`counterEmbeddingForcingInteriorEdgeWitness`,
`not_nonempty_boundaryFreeIncidentFaceSelector_counterEmbedding`, and
`counterEmbedding_directPositiveProjectedGeometryOn_and_forcingInteriorEdgeWitness` show that the
same embedding simultaneously carries both direct replacement-positive predicates and a forcing
edge.  The failed universals
`not_forall_not_nonempty_forcingInteriorEdgeWitness_of_theorem49HeightOrderedPositiveProjectedGeometryOn_counterGraph`,
`not_forall_not_nonempty_forcingInteriorEdgeWitness_of_theorem49CollarLayerPositiveProjectedGeometryOn_counterGraph`,
and
`not_forall_not_nonempty_forcingInteriorEdgeWitness_of_directPositiveProjectedGeometryOn_counterGraph`
therefore identify a hard ceiling on the forcing-edge route: forcing obstruction is a real
selector/construction-side blocker, but it cannot be promoted to a generic same-embedding
obstruction for the direct replacement-positive layer itself.  The same benchmark now also makes
that ceiling route-facing:
`counterEmbedding_directPositiveProjectedGeometryOn_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData`
shows that both direct replacement-positive predicates coexist on one embedding with failure of
both the boundary-free selector shell and the downstream construction face-layer package.
Accordingly,
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_directPositiveProjectedGeometryOn_counterGraph`
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_directPositiveProjectedGeometryOn_counterGraph`
show that direct replacement-positive geometry is not a generic source for either selector data
or construction-face-layer data on the same embedding.  The
same ceiling now also hits the residual/current-boundary wrapper on that benchmark:
`counterEmbedding_residualBoundaryPositiveProjectedGeometryOn_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData`,
`counterEmbedding_residualBoundaryPositiveProjectedGeometryOn_and_boundaryRootNonemptyProjectedSynthesis_and_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData`,
`counterGraph_explicitTait_residualBoundaryPositiveProjectedGeometry_and_boundaryRootNonemptyProjectedSynthesis_with_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData`,
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_theorem49ResidualBoundaryPositiveProjectedGeometryOn_counterGraph`,
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_theorem49ResidualBoundaryPositiveProjectedGeometryOn_counterGraph`
show that even after passing through the residual positive shell, and even once the projected
theorem-4.9 endpoint is already present on the same embedding, the two-collar benchmark still
does not force the selector or downstream construction-face-layer packages there.
The
generic graph-level
bridge is now factored into
`Theorem49PositiveGeometricSourceReplacement.lean`: an existential annulus collar geometry, or
repaired previous-boundary witness geometry, paired with nonempty purified carrier gives both
replacement graph packages and, with any supplied Tait coloring, the graph-level nonempty
projected synthesis endpoint itself.  A weaker acyclic witness-cover input is now sufficient too:
explicit well-founded parent witness-cover data plus `HasUnblockedInteriorEndpoint` reaches the
same projected synthesis endpoint, with an honest closed-walk source retained in the route-facing
statement for traceability.  This has now been pushed back through the root-distance
interior-dual route: honest closed-walk source data, or the equivalent successor-cycle source
fields, plus generic boundary-root interior-dual adjacency-distance data and
`HasUnblockedInteriorEndpoint` reach the same nonempty projected synthesis endpoint.  The same
source-facing root-distance bridge now exposes the raw Definition 4.8 quotient/error package by
`theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint`
and the successor-cycle analogue
`theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint`.
The same direct lane now also has graph-level existential wrappers:
`exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct`
and
`exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint_direct`.
The carrier side of this construction now factors through the named
predicate `HasUnblockedInteriorEndpoint`, and the route file can derive that witness from raw
`interiorEdgeEndpointSupport` nonemptiness plus either global endpoint-support disjointness or
peeled-face endpoint no-touch on the root-distance annulus construction.  The raw endpoint
carrier itself now follows from nonempty `interiorEdgeSupport`, so future source-facing examples
can state the carrier burden as an actual interior edge together with a global endpoint-support
separation theorem or a root-distance peeled-face no-touch theorem.

### Investigation strategy

1. **Construct the replacement package surface**
   - Treat `Theorem49SuccessorCycleCanonicalPositiveGeometry` and
     `Theorem49SuccessorCycleOneCollarPositiveGeometry` as refuted targets under the current
     carrier
   - Build `Theorem49HeightOrderedPositiveProjectedGeometry` or
     `Theorem49CollarLayerPositiveProjectedGeometry` directly from route-facing geometry
   - Keep any successor-cycle or closed-walk source shell as supporting geometry, not as a
     canonical-choice or one-collar nonempty endpoint

2. **Use countermodels as guards, not as the main route**
   - The shared-interior-pair and chained-diamonds regressions rule out arbitrary collars and
     missing source-tied geometry
   - The package-level impossibility rules out treating canonical witness choice or
     source-preserving one-collar geometry as the non-vacuous construction path
   - Bare source-preserving current-boundary data is now too weak to be a target: it is
     already automatic from honest source boundary data, and the shared-interior-pair model
     carries its one-collar instance

3. **Characterize the missing construction step**
   - The diamond benchmark has source-tied synthesis but empty purified carrier
   - The diamond benchmark now also has a concrete end-to-end source-to-Theorem49 raw package:
     `diamondWithTriangle_closedWalkSource_explicitTait_atMostOne_to_theorem49RawQuotientErrorPackage`
     bundles the honest closed-walk source, explicit Tait coloring, at-most-one source route,
     and the resulting raw Definition 4.8 representative plus selected-boundary-kernel error
     decomposition for every Kirchhoff chain on the same embedding
   - Even with that source-tied synthesis, the diamond benchmark has empty purified carrier
   - The same carrier collapse now blocks the projected endpoint itself:
     `not_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangle` rules out
     `Theorem49BoundaryRootNonemptyProjectedSynthesis` on the diamond-with-triangle embedding
     for every coloring
   - The new theorem
     `diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_nonemptyProjectedSynthesis`
     seals that comparison on the same genuine cyclic source model: the full current
     same-embedding positive geometry stack, together with explicit-Tait theorem-4.9 synthesis,
     already exists on `diamondWithTriangleEmbedding`, yet the newer projected nonempty endpoint
     still fails there because the selected-boundary-purified carrier is empty
   - This is now route-facing at graph level too:
     `exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph`
     and
     `not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph`
     show that even an honest closed-walk source together with canonical witness choice,
     explicit Tait coloring, annulus collar geometry, repaired previous-boundary witness
     geometry, all currently sufficient peel witnesses, and the full theorem-4.9 synthesis
     package still does not generically force the projected nonempty endpoint
   - The wheel benchmark has an honest closed-walk annulus source, Tait coloring, and nonempty
     carrier, but fails canonical choice, one-collar geometry, the raw
     well-founded/height-ordered/collar-layer witness-cover surfaces, and weak annulus-collar
     geometry itself because its three interior spokes force a strict dependency cycle; the same
     cycle now also blocks the direct height/collar positive replacement predicates and repaired
     previous-boundary witness geometry on that fixed embedding.  The forcing-edge regression
     now also proves
     `wheelWithInnerTriangle_closedWalkSource_tait_hasUnblockedEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData`,
     so the same concrete source has the honest source, explicit Tait coloring, and local
     unblocked endpoint required by the raw source-IDBRAD bridge while generic IDBRAD itself is
     impossible.
   - `Theorem49PositiveGeometricSourceRegression.lean` records the package-level version of
     that wheel calibration on the fixed embedding
   - `Theorem49PositiveGeometricSourceImpossibility.lean` proves the stronger structural
     diagnosis: the current package fields themselves imply empty carrier
   - The same file now gives the live-endpoint form of that diagnosis:
     `not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice`
     and
     `not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_oneCollarGeometry_with_sourceBoundaryData`
     state directly that the old canonical-choice and source-preserving one-collar branches
     have no local unblocked endpoint; equivalently,
     `not_nonempty_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint`
     and
     `not_exists_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint`
     rule those branches out from an honest source plus `HasUnblockedInteriorEndpoint`
   - `Theorem49PositiveGeometricSourceReplacement.lean` supplies the exact positive endpoint:
     the missing step is constructing one of its direct witness-data packages in a benchmark or
     in a general boundary-order theorem
   - `Theorem49PositiveGeometricSourceConstruction.lean` completes the benchmark side for the
     two-collar annulus and now reaches the nonempty projected synthesis endpoint for an explicit
     Tait coloring; it also exposes the corresponding raw quotient/error package through
     `counterEmbedding_collarGeometry_explicitTait_nonemptyCarrier_to_theorem49RawQuotientErrorPackage`.
     The companion theorem
     `counterEmbedding_rawQuotientErrorPackage_without_closedWalkAnnulusBoundarySource` proves
     that this same concrete benchmark still cannot supply an honest closed-walk annulus source.
     The remaining hard step is to produce the generic bridge hypotheses from natural
     route-facing source data
   - The carrier part of that hard step is now a first-order endpoint witness obligation:
     prove `HasUnblockedInteriorEndpoint` by producing an interior support edge and a chosen
     endpoint disjoint from the selected boundary endpoint support
   - Such a source-facing endpoint witness cannot live in the facewise at-most-one branch:
     `exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint`
     forces a two-interior-edge face for any honest closed-walk source with that witness
   - If the geometry is given as explicit well-founded parent witness-cover data, the positive
     side is now complete: pair that acyclic data with either `HasUnblockedInteriorEndpoint` or
     endpoint-support separation plus a raw endpoint carrier, then apply the direct
     projected-synthesis bridge
   - If the source-facing geometry is given as honest closed-walk source data plus generic
     boundary-root interior-dual adjacency-distance data, the acyclic witness-cover side is now
     available directly:
     `planarBoundaryHeightOrderedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData`
     turns the root-distance well-founded parent witness into height-ordered witness-cover data
     on the same embedding, and
     `admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_direct`
     exposes the graph-level source theorem.  The minimal upstream lemma still missing from the
     raw source route is a same-embedding construction of
     `InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary`, or an equivalent
     cycle-breaking well-founded parent witness, from the source-level boundary-order hypotheses.
     Once that datum and `HasUnblockedInteriorEndpoint` are available, the route now reaches the
     raw quotient/error endpoint directly through
     `theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint`
     and its successor-cycle counterpart.  The same live successor-cycle shell now also reaches the
     non-vacuous two-sided annulus-root synthesis surface on this generic IDBRAD lane:
     `theorem49AnnulusRootNonemptySynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport`
     and
     `exists_theorem49AnnulusRootNonemptySynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_with_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport`
     show that peeled-face endpoint no-touch for the canonical annulus construction, together with
     a nonempty raw interior-edge endpoint carrier, is already enough to reach
     `Theorem49AnnulusRootNonemptySynthesis` on the actual boundary-order shell, before any
     parent-cover package is introduced.
     `Theorem49PlanarBoundaryAnnulusRootInteriorDual.lean` now gives the precise source-side
     primitive constructor for that target:
     `interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceCoverSeparatedAnnulusBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover`
     consumes an honest closed-walk source plus cover/separated roots, boundary-free peeled
     faces, canonical rooted shared-edge coverage of every interior edge, child-face membership
     with strict root-distance increase, and the two-incidence bound.  The graph-level theorem
     `admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_exists_closedWalkAnnulusBoundarySource_and_coverSeparatedAnnulusBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover`
     exposes the same obligation as the current source-side route endpoint.  Thus the remaining
     source attack is no longer a search for an unnamed package: it is the concrete production
     of those rooted-peel fields from the boundary-order source.
     The sharper constructor
     `interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover`
     now fixes the root set to the outer-or-inner boundary faces extracted from the source and
     fixes the fallback edge to the source's honest facial closed-walk fallback; the embedding
     itself supplies the two-incidence bound.  So the live source-side IDBRAD burden is down to
     cover/separation of these source boundary-face roots, boundary-free peeled faces, interior
     edge coverage by rooted shared edges, and strict root-distance child membership.
     The actual successor-cycle boundary-order shell now has the matching downward route package:
     `interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover`
     and
     `admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover`.
     The same concrete rooted-cover package on the honest closed-walk source now also closes
     directly at full theorem-4.9 through
     `exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_direct`,
     so even on that source-facing shell there is no further theorem-4.9-side repackaging below
     the named rooted shared-edge face-membership burden.
     So once the live shell carries exactly that source-fixed rooted shared-edge face-membership
     cover package, no further source-to-IDBRAD repackaging step remains before the generic
     boundary-root route.  The same package now also closes directly at the theorem-4.9 endpoint
     through
     `exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_direct`,
     so no additional theorem-4.9-side repackaging remains below that concrete rooted-cover
     surface either.  The converse pressure point is now formalized at that same layer:
     `false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_reachable_outerBoundaryFace_innerBoundaryFace`
     and
     `not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_reachable_outerBoundaryFace_innerBoundaryFace`
     show that if the live shell still extracts an outer boundary face reaching an inner boundary
     face in the interior dual, then even the rooted shared-edge face-membership burden itself is
     impossible, before generic IDBRAD or theorem-4.9 packaging is invoked.
     The sufficiency side now also has the corresponding parent-oriented construction:
     `PlanarBoundaryClosedWalkAnnulusBoundarySource.wellFounded_parentRel_boundaryFaceRoots_parentTowardsRoot`
     proves that cover/separated source boundary-face roots induce a well-founded canonical
     shortest-path parent orientation, and
     `interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover`
     packages the same fixed roots and source fallback edge into
     `InteriorDualBoundaryRootParentPeelData` once rooted shared-edge coverage is supplied; the
     canonical parent child-membership field is now derived internally from that cover and the
     ambient two-incidence bound by `canonicalParentChildMembership_of_canonicalParentCover`.
     The graph-level theorem
     `admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover`
     exposes this raw-cover package as the source-fixed acyclic-parent sufficiency endpoint.  The
     older face-membership-cover constructor and graph theorem remain explicit compatibility
     surfaces for callers that already have the derived field.  The actual successor-cycle
     boundary-order shell now has the matching downward route package:
     `admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover`,
     `admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover`,
     and the two direct graph-level synthesis endpoints
     `exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_direct`
     and
     `exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_direct`.
     These all lower through
     `PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields`, so once the live
     successor-cycle shell carries the concrete source-fixed canonical-parent cover package, no
     further projection or repackaging step remains before
     `Theorem49BoundaryRootSynthesis`.
     The constructive branch now has a proved degenerate base case:
     `interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges`
     and
     `admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges`
     build the same source-fixed parent package with `peelFaces = ∅` whenever the source
     boundary-face roots cover/separate and `interiorEdgeSupport = ∅`.  Thus the remaining
     no-interior-edge branch is fully explicit.  The forcing file now sharpens this further:
     `exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover`
     and
     `interiorEdgeSupport_eq_empty_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover`
     show that under the current honest closed-walk or successor-cycle source semantics, the raw
     canonical-parent cover shell itself already collapses to `interiorEdgeSupport = ∅`.  So this
     source-fixed raw-cover package is no longer a live nondegenerate parent-source target unless
     the route changes the source interface.  The empty-support case also proves its own shared-edge uniqueness via
     `pairwiseUniqueSharedInteriorEdges_of_interiorEdgeSupport_eq_empty`, so this degenerate
     branch has no separate pairwise-uniqueness input.
     The nonempty branch now has a constructor-side sanity theorem rather than only downstream
     selector consequences.  The generic lemma
     `exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_canonicalParentCover_of_mem_interiorEdgeSupport`
     proves that any interior edge covered by the canonical rooted shared-edge image is covered
     by a peeled non-root face with an actual shortest-path parent, and that the rooted shared
     edge on that face is exactly the original interior edge.  Its nonempty-support corollary
     `exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_canonicalParentCover_of_interiorEdgeSupport_nonempty`
     makes the nondegenerate branch explicit at the forest layer.  The source-fixed
     specializations
     `exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_mem_interiorEdgeSupport`
     and
     `exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_interiorEdgeSupport_nonempty`
     instantiate the same result using the closed-walk source's boundary-face roots and fallback
     edge.  This confirms that the nonempty canonical-parent cover cannot be satisfied by the
     fallback branch.  The same pass also added parent-side face-membership lemmas for canonical
     shared edges and uses them to prove
     `canonicalParentChildMembership_of_canonicalParentCover`: every non-witness edge on a peeled
     face is either selected boundary support or belongs to a peeled child whose canonical parent
     is the original face.  This removes `hchildren` from the source-fixed parent constructor;
     the remaining geometric burden is to prove or supply the pairwise-unique shared-edge selector
     input and the source-fixed root cover/separation, boundary-free peeled-face, and rooted
     shared-edge cover hypotheses from boundary-order data.
     The positive source-fixed cross-check now instantiates that base case on a concrete
     closed-walk source in
     `Theorem49PlanarBoundaryAnnulusRootInteriorDualPositiveRegression.lean`: the disjoint
     two-triangle source `twoTriangleClosedWalkAnnulusBoundarySource` has
     `twoTriangleAnnulusBoundaryFaceRoots_eq_univ`, covers and separates those roots because
     the interior dual is `⊥`, proves `twoTriangleAnnulus_interiorEdgeSupport_eq_empty`, and
     constructs
     `twoTriangleClosedWalkSourceInteriorDualBoundaryRootParentPeelData` plus the graph-level
     `admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_twoTriangleAnnulusGraph`.
     The same positive example now reaches the selector-valued surface used by the replacement
     construction lane:
     `boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData` extracts a
     `BoundaryFreeIncidentFaceSelector` from any parent payload while preserving the actual
     parent cover through
     `boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_faceOf_mem_peelFaces`
     and
     `rootedSharedInteriorEdge_boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_faceOf_eq`.
     The construction-layer theorem
     `boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_peelFaces_subset`
     says the selector's finite peeled-face image introduces no faces beyond the parent package's
     `peelFaces`.  The source-fixed constructor
     `boundaryFreeIncidentFaceSelectorOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges`
     specializes this to the empty-support branch, and
     `twoTriangleClosedWalkSourceBoundaryFreeIncidentFaceSelector` instantiates it on the
     concrete two-triangle source.  So the base case is not only inhabited as parent data; it
     produces the exact selector object consumed by downstream boundary-free construction code.
     The parent-to-selector bridge now also supplies the strict-descent data required by that
     construction lane.  The parent-derived selector is injective on interior edges by
     `boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_injective`;
     on each selected face its inverted witness is exactly the canonical rooted shared edge by
     `boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_selectedWitnessEdge_eq`;
     and
     `boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_strictDescent`
     turns canonical parent child-membership into the selector `hrest` condition with root
     distance as the face distance.  Consequently
     `theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector`
     and
     `exists_theorem49HeightOrderedPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`
     already expose the packaged height-ordered positive geometry surface on that shell, and
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector`
     composes the same source-fixed parent hypotheses through the selector-to-construction
     surface directly.  This selector route now also has the downstream same-embedding and
     graph-level full closures
     `theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector`,
     `theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector`
     and
     `exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     `exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     `exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     so graph-level source data plus the local endpoint witness can use the selector path
     all the way to full theorem-4.9 synthesis and the graph-level raw quotient/error package
     without first repackaging the carrier as raw selected-boundary nonemptiness.  The live
     successor-cycle selected-arc shell now inherits the same stricter face-membership selector
     package too via
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector`,
     `theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector`,
     `theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector`,
     `theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector`,
     `exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     and
     `exists_theorem49HeightOrderedPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     `exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     `exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`.
     But the
     current honest-source semantics also make that stronger endpoint-consuming shell vacuous:
     `not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover`,
     `not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover`,
     and the matching graph-level no-coexistence theorems
     `not_exists_embedding_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint`
     and
     `not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint`
     show that the stricter child-membership shell cannot actually coexist with the named local
     endpoint witness on the same honest source surfaces.  So those selector/projected
     face-membership wrappers are presently route-diagnostic, not inhabited.  More sharply, the
     generic converse theorems
     `not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint`
     and
     `not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint`,
     together with the seed-free shared-interior-pair instances
     `not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
     and
     `not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`,
     show that no Tait coloring or exact v23 residual seed is needed to refute a universal
     derivation of that stronger shell.  The weaker raw canonical-parent shared-edge-cover shell
     is no longer only a projected endpoint either:
     `theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector`,
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector`,
     `theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector`,
     `theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector`,
     `exists_theorem49HeightOrderedPositiveProjectedGeometryOn_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     `exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     and
     `exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     `exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`.
     So once the honest closed-walk shell carries that raw cover together with
     `HasUnblockedInteriorEndpoint`, the selector lane already closes at packaged
     `Theorem49HeightOrderedPositiveProjectedGeometryOn`, full
     `Theorem49BoundaryRootSynthesis`, and the graph-level raw quotient/error package on the same
     embedding; the remaining source-facing selector burden there is only to derive the raw cover
     and endpoint witness themselves.
     The same shared-interior-pair benchmark now also
     bundles the whole local selector/canonical-parent burden at once:
     `not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
     and
     `not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
     show that honest source data or the live successor-cycle selected-arc shell, even after
     adding a Tait coloring, still do not universally force any of the local
     `BoundaryFreeIncidentFaceSelector`, raw canonical-parent shared-edge cover, stricter
     canonical-parent face-membership cover, or previously known same-embedding residual,
     height-ordered, collar-layer, attached-certificate, well-founded, or annulus-collar
     geometry surfaces from `HasUnblockedInteriorEndpoint` alone.  So this endpoint-only
     obstruction now blocks the whole local selector/parent ladder, not just one stronger
     endpoint shell at a time.  And this is no longer only a benchmark-facing statement:
     `not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint`
     and
     `not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint`
     lift that whole bundled failure pattern to reusable witness-based converses, so any
     same-embedding example with honest-source or live successor-cycle data, a Tait coloring,
     and `HasUnblockedInteriorEndpoint` but without the local selector/canonical-parent/known-
     geometry package already refutes a universal derivation of that whole burden.
     `Theorem49ResidualBoundaryObstruction.lean` now tightens the same diagnosis on the exact
     one-collar/v23 shared-interior-pair shell itself via
     `exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_sharedInteriorPair`,
     `exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_sharedInteriorPair`,
     `not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`,
     and
     `not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`.
     So even after adding exact one-collar current-boundary data and the exact v23 residual seed,
     the live shared-interior-pair benchmark still fails the whole bundled local
     selector/canonical-parent/known-geometry workaround class in one theorem, not merely its
     individual branches.  And this exact-shell bundled obstruction is now reusable too:
     `not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
     and
     `not_forall_some_selectorOrCanonicalParentOrKnownSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
     lift the same exact one-collar/v23 bundled failure pattern to witness-based converses, so
     any same-embedding exact-shell example with a Tait coloring, `HasUnblockedInteriorEndpoint`,
     and nonempty `V23ResidualBoundaryInitialState` but without the selector/canonical-parent/
     known-geometry package already refutes a universal derivation of that exact-shell burden.
     The same shared-interior-pair shell now also fails the earliest selector target directly:
     `exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_sharedInteriorPair`,
     `exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_sharedInteriorPair`,
     `not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`,
     and
     `not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`.
     So on the exact one-collar/v23 shell the earliest same-embedding selector burden already
     fails directly, not only as one disjunct inside the larger bundled workaround theorem.
     The same exact-shell shared-interior-pair benchmark now also fails the next construction
     surface directly:
     `exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair`,
     `exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData_sharedInteriorPair`,
     `not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`,
     and
     `not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`.
     So the exact one-collar/v23 shell now fails not only the earliest selector package but also
     the selected-boundary-contact construction package consumed by the later synthesis route.
     The selector lane
     now also closes directly at full theorem-4.9 synthesis on its own construction surface:
     `theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstruction_and_hasUnblockedInteriorEndpoint`
     and
     `BoundaryFreeIncidentFaceSelector.theorem49BoundaryRootSynthesis_of_strictDescent_and_hasUnblockedInteriorEndpoint`
     show that once an injective strict-descent selector and a local endpoint witness exist on
     an embedding, no further projected-synthesis packaging remains below the selector-built
     annulus construction.  The actual successor-cycle boundary-order shell now has the matching
     raw-cover selector route too:
     `theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector`,
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector`,
     `theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector`,
     `theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector`,
     and
     `exists_theorem49HeightOrderedPositiveProjectedGeometryOn_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     `exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     `exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     `exists_theorem49BoundaryRawQuotientErrorPackage_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`.
     So once the live successor-cycle shell carries the raw canonical-parent shared-edge cover
     together with `HasUnblockedInteriorEndpoint`, it already reaches the selector-built
     annulus-construction lane, packaged `Theorem49HeightOrderedPositiveProjectedGeometryOn`,
     full `Theorem49BoundaryRootSynthesis`, and the graph-level raw quotient/error package
     directly, without a residual-boundary detour; the remaining
     source-facing selector burden is only to derive that injective strict-descent selector
     package itself on the live shell.  The same
     raw-cover selector lane now also exposes the
     route-facing terminal selected-face break rather than only its downstream projected
     consequences:
     `exists_terminal_face_boundary_remainders_and_disjoint_of_interiorDualBoundaryRootParentPeelData_via_boundaryFreeSelector`
     lifts the generic selector terminal-face theorem to any canonical-parent parent package, and
     the source/raw/live-shell specializations
     `exists_terminal_face_boundary_remainders_and_disjoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector`,
     `exists_terminal_face_boundary_remainders_and_disjoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector`
     and
     `exists_terminal_face_boundary_remainders_and_disjoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector`,
     together with
     `exists_terminal_face_boundary_remainders_and_disjoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector`
     show that both the stricter face-membership shell and the raw canonical-parent cover shell,
     plus `HasUnblockedInteriorEndpoint`, already yield a peeled face whose non-witness
     remainders lie on the ambient annulus boundary while its full face boundary remains
     disjoint from selected-boundary support.  So the live selector compatibility lane now
     reaches an explicit same-shell terminal boundary-break witness before any
     residual-boundary or collar-layer packaging, even before discarding the child-membership
     refinement.  The weaker boundary-root adjacency-distance shell now also factors explicitly
     through this same selector lane:
     `exists_terminal_face_boundary_remainders_and_disjoint_of_interiorDualBoundaryRootAdjDistancePeelData_via_boundaryFreeSelector`,
     `theorem49HeightOrderedPositiveProjectedGeometryOn_of_interiorDualBoundaryRootAdjDistancePeelData_via_boundaryFreeSelector`,
     `theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootAdjDistancePeelData_via_boundaryFreeSelector`,
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootAdjDistancePeelData_via_boundaryFreeSelector`,
     and
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_via_boundaryFreeSelector`
     show that once generic boundary-root adjacency-distance data and
     `HasUnblockedInteriorEndpoint` are present on an embedding, the canonical upgrade to the
     parent shell already recovers the selector terminal boundary-break, height-ordered
     positive geometry, and projected theorem-4.9 endpoint without leaving the selector-built
     annulus-construction architecture.
     `PlanarBoundaryClosedWalkSourceProjection.lean` now composes this source-fixed parent
     endpoint through the existing height/collar witness route to the nonempty projected
     Theorem 4.9 package via
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_direct`
     and the graph-level existential wrapper
     `exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct`.
     The concrete wheel-with-inner-triangle regression now instantiates this source-fixed
     parent bridge at the actual projected endpoint:
     `wheelWithInnerTriangle_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover`
     specializes the direct theorem to the wheel embedding and its explicit Tait coloring.
     The same hypotheses lower back to height-ordered witness-cover data, so
     `wheelWithInnerTriangle_source_to_theorem49_and_height_cycle_contradiction_of_closedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover`
     contradicts the existing wheel height-cycle obstruction.  Thus
     `not_exists_wheelWithInnerTriangle_closedWalkSourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_theorem49BoundaryRootNonemptyProjectedSynthesis`
     is the endpoint-level sanity check: the wheel has the honest source, Tait coloring, and
     unblocked endpoint, but cannot instantiate the new source-fixed parent route.
     The coverage half of this fixed-root burden is now calibrated:
     `PlanarBoundaryClosedWalkAnnulusBoundarySource.rootSetCovers_boundaryFaceRoots_of_interiorDualBoundaryRootAdjDistancePeelData`
     shows that any existing generic boundary-root IDBRAD datum already makes the source
     boundary-face root set cover the interior-dual components.  Separation is the real
     fixed-root obstruction:
     `PlanarBoundaryClosedWalkAnnulusBoundarySource.not_rootSetSeparated_boundaryFaceRoots_of_reachable_outerBoundaryFace_innerBoundaryFace`
     refutes separated source boundary-face roots as soon as an outer boundary face reaches an
     inner boundary face in the interior dual.
     The same diagnosis now exists at the generic IDBRAD layer:
     `PlanarBoundaryClosedWalkAnnulusBoundarySource.not_reachable_outerBoundaryFace_innerBoundaryFace_of_interiorDualBoundaryRootAdjDistancePeelData`
     proves that any IDBRAD datum on the closed-walk source forces those extracted boundary-face
     layers to be interior-dual reachability-separated, and
     `PlanarBoundaryClosedWalkAnnulusBoundarySource.not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_reachable_outerBoundaryFace_innerBoundaryFace`
     records the failed-converse form.
     The graph/source-facing no-coexistence and failed-universal wrappers
     `not_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_reachable_outerBoundaryFace_innerBoundaryFace`
     and
     `not_forall_interiorDualBoundaryRootAdjDistancePeelData_of_exists_closedWalkAnnulusBoundarySource_and_reachable_outerBoundaryFace_innerBoundaryFace`
     expose the same obstruction without asking downstream route files to unpack the source
     object manually.
     The live successor-cycle shell now inherits even that earlier source boundary-face
     separation failure directly:
     `not_rootSetSeparated_boundaryFaceRoots_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_reachable_outerBoundaryFace_innerBoundaryFace`
     and
     `not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_rootSetSeparated_boundaryFaceRoots_and_reachable_outerBoundaryFace_innerBoundaryFace`
     show that if actual boundary reachability plus successor-cycle data still extract an
     outer-to-inner interior-dual path, then the route already dies at the source `hsepRoots`
     premise itself, before any rooted shared-edge cover or generic IDBRAD payload is in play.
     The live successor-cycle shell now inherits that same source-side obstruction directly:
     `not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_reachable_outerBoundaryFace_innerBoundaryFace`
     and
     `not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData_and_reachable_outerBoundaryFace_innerBoundaryFace`
     show that if the source extracted from actual boundary reachability and successor-cycle data
     still has an interior-dual path from one outer boundary face to one inner boundary face, then
     the route already fails before the source-fixed rooted-cover IDBRAD bridge or any theorem-4.9
     endpoint is invoked.
     `Theorem49PlanarBoundaryAnnulusRootInteriorDualObstructionRegression.lean` now instantiates
     that source-side obstruction on the concrete two-band triangular annulus
     `twoBandAnnulusGraph`: it proves the honest closed-walk source package
     `twoBandClosedWalkAnnulusBoundarySource`, the outer-to-inner interior-dual adjacency
     `twoBandAnnulus_interiorDual_adj_outer0_inner0`, and the concrete nonexistence theorem
     `not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_twoBandAnnulus_via_source_reachability`.
     The same benchmark is now upgraded to an actual successor-cycle shell:
     `twoBandAnnulusDartSuccessorCycleGeometry` and
     `twoBandAnnulusDartSuccessorCycleGeometry_selectedBoundaryArcOnFace` instantiate the live
     route surface, while
     `twoBandDartSuccessorClosedWalkAnnulusBoundarySource_boundaryData_eq` and
     `twoBandDartSuccessorBoundaryFaceRoots_eq_univ` show that this live shell extracts the same
     annulus boundary split and the same full six-face boundary-root set as the closed-walk
     source,
     `rootSetCovers_twoBandDartSuccessorBoundaryFaceRoots` makes the coverage half explicit there
     too, and
     `not_rootSetSeparated_twoBandAnnulusBoundaryFaceRoots_via_dartSuccessor_source_reachability`
     and
     `not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_twoBandAnnulus_via_dartSuccessor_source_reachability`
     show that the same outer-to-inner interior-dual adjacency already kills only the source
     `hsepRoots` premise, and hence generic IDBRAD data, before any rooted-cover or theorem-4.9
     packaging is introduced.  The benchmark now also kills the live rooted-cover burden itself:
     `not_exists_twoBandAnnulus_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_via_dartSuccessor_source_reachability`
     proves that no boundary-free peeled-face set, rooted shared-edge cover, and strict
     child-membership witnesses can coexist with that same extracted outer-to-inner
     interior-dual reachability on the actual successor-cycle shell.
     The same concrete source now separates coverage from separation for the fixed source roots:
     `twoBandAnnulusBoundaryFaceRoots_eq_univ` proves that the source-extracted
     `boundaryFaceRoots` are all six faces,
     `rootSetCovers_twoBandAnnulusBoundaryFaceRoots` proves the cover premise, and
     `not_rootSetSeparated_twoBandAnnulusBoundaryFaceRoots` proves the separation premise false
     using the same outer-to-inner adjacency through `tbaM01`.
     The regression also proves the primitive peel obstruction
     `twoBandAnnulus_peelFaces_eq_empty_of_boundaryFree`: every face touches selected boundary
     support, so any boundary-free peel-face set is empty.  Since `tbaM01` is an interior edge,
     `not_interiorEdgeSupport_subset_boundaryFreePeelImage_twoBandAnnulus` rules out covering
     the interior-edge support by any image of such boundary-free peel faces.
     This is now tied back to the shared forcing-edge API:
     `twoBandAnnulusForcingInteriorEdgeWitness` packages `tbaM01` as a
     `ForcingInteriorEdgeWitness`,
     `not_nonempty_boundaryFreeIncidentFaceSelector_twoBandAnnulus` rules out the selector
     form, and
     `not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_twoBandAnnulus_via_forcingInteriorEdgeWitness`
     gives an independent forcing-edge proof of the same IDBRAD nonexistence.
     The forcing obstruction now also reaches the source-fixed parent target directly:
     `everyInteriorEdgeHasBoundaryFreeIncidentFace_of_interiorDualBoundaryRootParentPeelData`
     extracts a boundary-free incident face from any canonical-parent boundary-root package,
     while `not_nonempty_interiorDualBoundaryRootParentPeelData_twoBandAnnulus_via_forcingInteriorEdgeWitness`
     and
     `not_nonempty_planarBoundaryAnnulusRootParentPeelData_twoBandAnnulus_via_forcingInteriorEdgeWitness`
     show that the same honest two-band source cannot instantiate the parent-oriented
     sufficiency branch either.  The same forcing witness now blocks the live theorem-4.9 raw
     canonical-parent cover shell one layer earlier:
     `false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_forcingInteriorEdgeWitness`
     and
     `not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_forcingInteriorEdgeWitness`
     show that once a successor-cycle shell carries a forcing interior edge, no raw
     canonical-parent shared-edge cover package can exist on that shell at all.
     The two-band benchmark now instantiates this directly as
     `not_exists_twoBandAnnulus_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_forcingInteriorEdgeWitness`,
     so the live parent-cover lane already fails there before any parent-peel or theorem-4.9
     synthesis packaging is invoked.  The same benchmark now also kills the older raw carrier
     repair on that exact shell:
     `not_exists_twoBandAnnulus_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport`
     shows that even endpoint-support separation plus a nonempty raw interior-edge endpoint
     carrier cannot rescue the live parent-cover lane on the actual successor-cycle benchmark.
     The generic IDBRAD layer now also exposes the terminal leaf obstruction directly in
     `Theorem49PlanarBoundaryPeeling.lean`:
     `PlanarBoundaryHeightOrderedFacePeelWitnessData.exists_terminal_face_selectedBoundary_remainders`
     says any nonempty height-ordered witness cover has a peeled face whose non-witness
     remainders are all selected-boundary edges.  Adding the IDBRAD boundary-free peeled-face
     invariant gives
     `InteriorDualBoundaryRootAdjDistancePeelData.exists_terminal_peelFace_witness_erase_eq_empty_of_mem_interiorEdgeSupport`,
     and hence
     `InteriorDualBoundaryRootAdjDistancePeelData.exists_peelFace_card_le_one_of_mem_interiorEdgeSupport`:
     any IDBRAD datum covering even one interior edge contains a peeled face with boundary
     cardinality at most one.  Thus a source-side construction of IDBRAD must either explain this
     terminal singleton-edge face or replace the IDBRAD package with a different witness-ownership
     surface.
     So the next source attack must derive real outer/inner face separation and a nontrivial
     boundary-free peel source, not another higher-level wrapper around the IDBRAD obstruction.
     Once that datum is present, the remaining carrier burden can be stated as a local endpoint
     witness, endpoint-support separation with a raw carrier, or peeled-face endpoint no-touch on
     the root-distance construction with a raw carrier
   - Existing endpoint-separated annulus data can now discharge that carrier obligation through
     raw `interiorEdgeEndpointSupport` nonemptiness and endpoint-support disjointness, then reuse
     the same annulus-collar or root-distance source projected-synthesis constructors
   - `Theorem49PositiveGeometricSourceReplacementRegression.lean` rules out deriving the direct
     or route-facing replacement predicates from boundary reachability, selected arcs, Tait
     coloring, and either carrier nonemptiness or the explicit
     `HasUnblockedInteriorEndpoint` witness in the shared-interior-pair model
   - The source-bearing wheel witness-cover obstruction identifies an additional
     construction-side requirement: the dependency relation generated by non-witness interior
     edges must be broken by selected boundary support or oriented by genuine well-founded parent
     data before it can support even the direct height/collar replacement surfaces, repaired
     previous-boundary witness geometry, or weak annulus-collar geometry
   - `PlanarBoundaryAnnulusConstructionCore.lean` now records the same maximum-distance fact at
     the central construction surface:
     `PlanarBoundaryAnnulusConstruction.exists_terminal_peelFace_boundary_remainders` says that
     every nonempty BFS-stratified annulus construction has a maximum-distance peeled face whose
     every non-witness remainder edge is already in the outer or inner ambient annulus boundary.
     The proof now factors through the named construction dependency relation
     `PlanarBoundaryAnnulusConstruction.remainderDependency`: a non-boundary remainder selected
     by the `hrest` field yields
     `PlanarBoundaryAnnulusConstruction.exists_remainderDependency_of_nonboundary_remainder`,
     while
     `PlanarBoundaryAnnulusConstruction.false_of_remainderDependency_cycle`,
     `PlanarBoundaryAnnulusConstruction.false_of_total_remainderDependency`, and
     `PlanarBoundaryAnnulusConstruction.exists_terminal_peelFace_no_remainderDependency`
     expose the finite strict-descent obstruction directly on the reusable construction surface.
     The local equivalence
     `PlanarBoundaryAnnulusConstruction.no_remainderDependency_iff_boundary_remainders`
     now identifies no outgoing construction dependency for a peeled face exactly with all
     non-witness remainders lying on the ambient annulus boundary; its forward direction is
     also named as
     `PlanarBoundaryAnnulusConstruction.boundary_remainders_of_no_remainderDependency`.
     The core construction file now also proves
     `PlanarBoundaryAnnulusConstruction.peelFaces_nonempty_of_mem_interiorEdgeSupport`,
     `PlanarBoundaryAnnulusConstruction.exists_terminal_peelFace_boundary_remainders_of_mem_interiorEdgeSupport`,
     and the corresponding nonempty-interior-support form, so callers no longer need to carry
     `data.peelFaces.Nonempty` as an independent side condition.  Thus a
     source-to-construction proof cannot hide the terminal boundary break inside the selector
     layer; it is a direct invariant of the strict-descent `hrest` field as soon as the
     construction actually covers a live interior edge.
   - `Theorem49PlanarBoundaryAnnulusConstructionOrientationObstruction.lean` now calibrates
     that last point against the parent-orientation target:
     `not_forall_live_planarBoundaryAnnulusConstruction_terminalNoDependency_implies_parentWitnessOrientation`
     shows that even live interior-edge support plus a terminal peeled face with no outgoing
     construction-level `remainderDependency` does not force
     `PlanarBoundaryAnnulusConstruction.ParentWitnessOrientation`.  The terminal boundary break
     is therefore a cycle-breaking diagnostic at the construction surface, not the missing
     well-founded parent-witness orientation itself.
     The same counterconstruction now lowers to both
     `PlanarBoundaryAnnulusConstructionPositiveFrontierData` and
     `PlanarBoundaryAnnulusConstructionBoundarySupportFaceData` while still refuting parent
     orientation, via
     `not_forall_planarBoundaryAnnulusConstructionPositiveFrontierData_implies_parentWitnessOrientation`
     and
     `not_forall_planarBoundaryAnnulusConstructionBoundarySupportFaceData_implies_parentWitnessOrientation`.
     Thus selected-boundary contact and positive current-frontier bookkeeping are not by
     themselves the missing well-founded parent witness.
     The obstruction has also been sharpened at the raw construction surface:
     `not_forall_planarBoundaryAnnulusConstruction_positive_faceDistance_implies_parentWitnessOrientation`
     shows that even requiring every peeled face to have positive stored distance does not force
     a strictly earlier incident parent face.  This is deliberately not a frontier-data repair:
     `PlanarBoundaryAnnulusConstructionPositiveFrontierData.exists_peelFace_faceDistance_zero`
     and `PlanarBoundaryAnnulusConstructionPositiveFrontierData.not_forall_peelFaces_positive`
     show that positive-frontier data itself necessarily has a zero-distance peeled stratum.  The
     core construction lemma
     `PlanarBoundaryAnnulusConstruction.not_forall_stratumFaces_nonempty_of_parentWitness`
     factors the clash at the stratum level: parent orientation empties the zero stratum, while
     the current positive-frontier axioms require every stratum to be inhabited.  The
     stronger core theorem
     `PlanarBoundaryAnnulusConstructionPositiveFrontierData.not_parentWitnessOrientation`,
     together with the face-partition and boundary-support variants, now records that these
     current-frontier shells are incompatible with strict parent-witness orientation as currently
     indexed.  The live issue is therefore the actual lower-distance incidence witness, not a
     scalar positivity condition or the present zero-based positive-frontier shell.
     `PlanarBoundaryAnnulusConstruction.lean` now makes the source-side mismatch explicit via
     `not_exists_planarBoundaryAnnulusConstructionPositiveFrontierData_with_rootDistanceConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData`:
     the parent-oriented root-distance construction produced by boundary reachability plus
     interior-dual boundary-root adjacency-distance data cannot be wrapped in the current
     positive-frontier shell.  Thus the positive root-distance route and the zero-based
     frontier bookkeeping route are genuinely different surfaces, not interchangeable views of
     one construction.  The construction file now also records the exact finite-set
     calibration behind the repair:
     `rootDistance_faceDistance_succ_filter_eq_shifted_faceDistance_filter_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData`
     says that root-distance layer `n + 1` on peeled faces is exactly shifted-construction
     layer `n`, with
     `rootDistance_faceDistance_one_filter_eq_shifted_faceDistance_zero_filter_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData`
     as the first-layer specialization.  The sharper diagnostic
     `rootDistance_faceDistance_one_filter_nonempty_iff_not_shifted_parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData`
     then identifies nonemptiness of root-distance layer `1` exactly with failure of strict
     parent-witness orientation for the shifted construction.
   - `Theorem49BoundaryFreeSelectorConstruction.lean` now exposes the same requirement in
     selector form.  A `BoundaryFreeIncidentFaceSelector` can be inverted into an annulus
     construction when selected faces are injective over interior edges and non-witness remainders
     satisfy strict descent.  The relation `remainderDependency` now names the selector-side
     dependency generated when the selected witness of one peeled face is a non-witness,
     non-boundary remainder edge of another; `faceDistance_lt_of_remainderDependency` turns each
     dependency into a strict face-distance inequality, and
     `false_of_remainderDependency_cycle` rules out every nonempty finite closed selector
     dependency chain under the same strict-descent hypothesis.  The new equivalence
     `toPlanarBoundaryAnnulusConstruction_remainderDependency_iff` shows that this selector
     relation is exactly the construction-level `PlanarBoundaryAnnulusConstruction.remainderDependency`
     relation after lowering a strict-descent selector to a construction; the extra construction
     face-distance field is recovered from selector `hrest`.  The companion
     `toPlanarBoundaryAnnulusConstruction_no_remainderDependency_iff` now shows that terminal
     no-dependency is also preserved exactly by the selector-to-construction lowering.  The
     selector side also has the construction-matching characterization
     `no_remainderDependency_iff_boundary_remainders`: on any selected face, having no outgoing
     selector dependency is equivalent to every non-witness remainder edge lying on the outer or
     inner ambient boundary.  The stronger maximum-distance
     obstruction `false_of_total_remainderDependency` rules out a nonempty selected-face set
     closed under outgoing remainder dependencies, and
     `exists_face_without_remainderDependency` exposes the corresponding terminal selected face
     where a source-to-selector construction must show an ambient-boundary break or some other
     cycle-breaking orientation.  The boundary-break theorem
     `exists_terminal_face_boundary_remainders` makes that positive local consequence explicit:
     for one selected face, every non-witness remainder edge already lies on the outer or inner
     ambient annulus boundary.  The variants
     `peelFaces_nonempty_of_mem_interiorEdgeSupport`,
     `exists_terminal_face_boundary_remainders_of_mem_interiorEdgeSupport`, and
     `exists_terminal_face_boundary_remainders_of_interiorEdgeSupport_nonempty` remove the
     separate selected-face nonemptiness premise when a live interior edge is available.  With
     the remaining
     non-peeled-face, separated-boundary, and positive current-frontier hypotheses supplied
     explicitly, it reaches
     `PlanarBoundaryAnnulusConstructionBoundarySupportFaceData` and therefore excludes forcing
     interior-edge witnesses on the same embedding.  The selector bridge is useful positive
     infrastructure, but it does not derive those frontier obligations from source data.
   - `Theorem49PositiveGeometricSourceReplacement.lean` now exposes the construction-level
     version of that positive endpoint:
     `theorem49HeightOrderedPositiveProjectedGeometryOn_of_planarBoundaryAnnulusConstruction`
     turns any `PlanarBoundaryAnnulusConstruction` plus a live purified carrier into the
     height-ordered replacement package, and
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstruction`
     adds a Tait coloring to reach the corrected nonempty projected synthesis endpoint.  The
     same hypotheses also expose
     `theorem49TerminalPeelFaceBoundaryRemainders_of_planarBoundaryAnnulusConstruction`, which
     turns the live purified carrier into a terminal peeled face whose non-witness remainders are
     already ambient-boundary edges.  The
     selector-positive module now factors through these construction-level theorems rather than
     unpacking the construction internals.  Thus a boundary-free selector with annulus boundary
     data, injectivity over interior edges, strict-descent remainders, and a live purified carrier
     is only one route into the reusable annulus-construction endpoint; the source-facing work
     remains to derive the selector compatibility, live carrier, and frontier obligations rather
     than assuming them.
     The selector-positive route now also has the local-endpoint form of this bridge:
     `BoundaryFreeIncidentFaceSelector.theorem49HeightOrderedPositiveProjectedGeometryOn_of_strictDescent_and_hasUnblockedInteriorEndpoint`
     and
     `BoundaryFreeIncidentFaceSelector.theorem49BoundaryRootNonemptyProjectedSynthesis_of_strictDescent_and_hasUnblockedInteriorEndpoint`
     consume `HasUnblockedInteriorEndpoint` directly, while
     `BoundaryFreeIncidentFaceSelector.exists_terminal_face_boundary_remainders_of_strictDescent_and_hasUnblockedInteriorEndpoint`
     exposes the same terminal boundary-break face from the named endpoint witness.  The base
     interior-vertex file supplies the small bridge
     `interiorEdgeSupport_nonempty_of_hasUnblockedInteriorEndpoint`, so this no longer has to be
     routed through raw carrier nonemptiness at selector call sites.  The sharpened diagnostic
     `BoundaryFreeIncidentFaceSelector.exists_terminal_face_boundary_remainders_and_disjoint_of_strictDescent_and_hasUnblockedInteriorEndpoint`
     records that this same terminal selected face still has the selector's full
     selected-boundary-support avoidance, so the exposed boundary break is not separated from the
     boundary-free incident-face condition.
   - `Theorem49ForcingInteriorEdgeObstructionRegression.lean` now also puts the selector
     alternative into the source-bearing wheel failed universal.  The wheel-with-inner-triangle
     benchmark has an honest closed-walk annulus source, a Tait coloring, and a nonempty purified
     selected-boundary carrier, but
     `not_nonempty_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle` rules out a
     boundary-free incident-face selector, and
     `not_forall_some_boundaryFreeSelector_or_acyclicEndpoint_of_closedWalkSource_tait_carrier_wheel`
     rules out the universal claim that those source/coloring/carrier hypotheses force either a
     selector or any current acyclic annulus endpoint.
     The obstruction file now names the underlying duality directly:
     `nonempty_boundaryFreeIncidentFaceSelector_iff_not_nonempty_forcingInteriorEdgeWitness`
     and
     `not_nonempty_boundaryFreeIncidentFaceSelector_iff_nonempty_forcingInteriorEdgeWitness`
     show that a boundary-free selector is exactly the absence of a forcing interior edge.
     Thus selector-based source attempts can be tested before construction lowering by either
     building the selector or exhibiting the forcing witness.
     The same obstruction file now also proves the direct interior-dual criterion
     `everyInteriorEdgeHasBoundaryFreeIncidentFace_of_interiorDualBoundaryRootAdjDistancePeelData`
     and its no-forcing corollary
     `not_nonempty_forcingInteriorEdgeWitness_of_interiorDualBoundaryRootAdjDistancePeelData`.
     These theorems use the `hcover` and `hpeelInterior` fields of
     `InteriorDualBoundaryRootAdjDistancePeelData`: every interior edge is assigned to a peeled
     witness face whose whole boundary avoids selected-boundary support.  Thus deriving the
     interior-dual boundary-root package from source data necessarily includes proving the same
     local no-forcing face-incidence condition, independently of any later construction or
     selector compatibility layer.  On the wheel-with-inner-triangle benchmark this obstruction
     is now stated in the exact source-bridge shape by
     `wheelWithInnerTriangle_closedWalkSource_tait_hasUnblockedEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData`:
     source data, Tait coloring, and `HasUnblockedInteriorEndpoint` coexist on one embedding,
     but `InteriorDualBoundaryRootAdjDistancePeelData` does not.
     The new terminal-face theorems in `Theorem49PlanarBoundaryPeeling.lean` strengthen the same
     diagnosis globally: if such an IDBRAD datum exists and covers an interior edge, one peeled
     face has no non-witness boundary edges and therefore has boundary cardinality at most one.
     This gives a direct source-side test for future attempts: any proposed boundary-order
     construction whose peeled faces are all genuine multi-edge faces cannot instantiate the
     current IDBRAD package.
     The wheel-with-inner-triangle regression now instantiates that test without using the
     forcing-edge API:
     `wheelWithInnerTriangleFaceBoundary_card_eq_three` and
     `wheelWithInnerTriangle_two_le_faceBoundary_card` prove that every ambient face in the source
     benchmark is a three-edge face, and
     `not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_terminal_card_lower_bound`
     refutes IDBRAD from `wit01_mem_interiorEdgeSupport` and this face-cardinality lower bound.
     The route-facing package
     `wheelWithInnerTriangle_closedWalkSource_tait_hasUnblockedEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData_via_terminal_card`
     keeps the honest source, Tait coloring, and local unblocked endpoint while deriving the
     IDBRAD contradiction through the terminal-card obstruction.
     The same file now also lifts this from a fixed wheel embedding to reusable failed
     converses on both live source shells:
     `exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangleGraph`
     and
     `not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangleGraph`
     show that honest closed-walk source data, a real Tait coloring, and
     `HasUnblockedInteriorEndpoint` still do not generically force same-embedding IDBRAD on
     the wheel graph; likewise
     `exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangleGraph`
     and
     `not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangleGraph`
     collapse the same converse on the actual successor-cycle boundary-order shell.
     The same concrete source is now also wired to the actual projected Theorem 4.9 endpoint:
     `wheelWithInnerTriangleGraph_edgeSet_fintype` supplies the finite edge-set instance,
     `hasUnblockedInteriorEndpoint_wheelWithInnerTriangle` names the endpoint witness, and
     `wheelWithInnerTriangle_theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootAdjDistancePeelData`
     proves that a hypothetical same-embedding IDBRAD datum reaches
     `Theorem49BoundaryRootNonemptyProjectedSynthesis` for the concrete Tait coloring.  The raw
     Definition 4.8 endpoint is exposed by
     `wheelWithInnerTriangle_theorem49BoundaryRawQuotientErrorPackage_of_interiorDualBoundaryRootAdjDistancePeelData`,
     while
     `wheelWithInnerTriangle_source_to_theorem49_and_terminal_card_contradiction_of_interiorDualBoundaryRootAdjDistancePeelData`
     records that the same datum would simultaneously trigger the terminal-card contradiction.
     This has also been repackaged exactly at the blocked endpoint:
     `not_exists_wheelWithInnerTriangle_closedWalkSource_and_interiorDualBoundaryRootAdjDistancePeelData_and_theorem49BoundaryRootNonemptyProjectedSynthesis`
     says that the closed-walk source, a same-embedding IDBRAD datum, and the projected Theorem
     4.9 endpoint cannot coexist on the wheel.  The bundled theorem
     `wheelWithInnerTriangle_closedWalkSource_tait_hasUnblockedEndpoint_without_interiorDualBoundaryRootAdjDistancePeelData_based_projectedSynthesis`
     keeps the positive source, Tait coloring, and unblocked endpoint while ruling out exactly
     an IDBRAD-based projected endpoint instantiation.
   - `PlanarBoundaryClosedWalkSourceCanonicalWitness.lean` now records the exact source-side
     canonical-witness criterion:
     `nonempty_planarBoundaryCanonicalWitnessChoice_iff_facewiseAtMostOneInteriorEdge_of_closedWalkAnnulusBoundarySource`
     says that, on an honest closed-walk annulus source, the source boundary split carries a
     canonical witness choice if and only if every face has at most one interior boundary edge.
     The graph-level existential form
     `exists_closedWalkAnnulusBoundarySource_and_planarBoundaryCanonicalWitnessChoice_iff_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge`
     makes the same equivalence available to source search.  Thus the source-side canonical
     witness attack is no longer an ambiguous construction-interface task: its exact remaining
     obligation is the facewise at-most-one condition, which the live-endpoint obstruction files
     already identify as incompatible with the current non-vacuous carrier.
     `PlanarBoundaryClosedWalkSourceRoute.lean` now also lowers that lane to the exact split
     annulus witness-ownership surface itself:
     `admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct`,
     `admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge_direct`,
     `admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_direct`,
     and
     `admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge_direct`.
     So on the canonical-witness lane, no annulus-decomposition or witness-assignment packaging
     burden remains below the facewise at-most-one condition itself.
     `Theorem49AtMostOneNonemptyCarrierImpossibility.lean` now instantiates that exact live
     successor-cycle facewise-at-most-one shell on the explicit diamond benchmark via
     `exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge_diamondWithTriangleGraph`,
     `diamondWithTriangleGraph_admitsPlanarBoundaryAnnulusWitnessAssignment_via_successorCycle_facewiseAtMostOneInteriorEdge`,
     and
     `exists_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_facewiseAtMostOneInteriorEdge`.
     Thus the live successor-cycle at-most-one branch is genuinely inhabited and already reaches
     witness assignment and theorem-4.9 synthesis on a concrete graph; the only attempted
     downstream upgrade on that branch is the nonempty-carrier endpoint, not basic route
     reachability.
     The same file now calibrates that constructive branch at the exact current-boundary layer as
     well:
     `exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph`
     shows that the same live successor-cycle shell already carries source-preserving one-collar
     current-boundary data while still supporting canonical witness assignment and explicit
     theorem-4.9 synthesis on the fixed diamond embedding.  But the same file now also proves
     `not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_hasUnblockedInteriorEndpoint`
     and
     `not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_hasUnblockedInteriorEndpoint`.
     So on this branch the exact current-boundary shell is not the missing burden either: the
     endpoint-bearing/nonempty-carrier upgrade itself is impossible on the current honest
     closed-walk and successor-cycle one-collar at-most-one interfaces.
     The same file now also proves the direct projected-endpoint collapses
     `not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge`,
     `not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_facewiseAtMostOneInteriorEdge`,
     `not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootNonemptyProjectedSynthesis`,
     and
     `not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootNonemptyProjectedSynthesis`.
     So even the actual current projected theorem-4.9 endpoint is structurally blocked on that
     shell, not just the intermediate endpoint witness.  The benchmark packages
     `exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph`
     and
     `exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph`
     record the same honest-source and successor-cycle exact-shell diagnosis on the explicit
     diamond embedding, and
     `diamondWithTriangleGraph_explicitTait_fixedEmbedding_oneCollarCurrentBoundary_facewiseAtMostOne_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis`
     together with
     `diamondWithTriangleGraph_explicitTait_fixedEmbedding_closedWalkOneCollarCurrentBoundary_facewiseAtMostOne_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis`
     package that same conclusion as fixed-embedding explicit-Tait graph-level theorems on the
     successor-cycle and honest-source shells respectively.
     The same file now also packages the stronger fallback/count/boundary-rest hypothesis surface
     on that benchmark via
     `exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph`,
     and then instantiates the first corrected projected Definition 4.8 endpoints as
     `exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_atMostOneInteriorEdgePerFace`
     and
     `exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_atMostOneInteriorEdgePerFace`.
     So the same live successor-cycle at-most-one shell already reaches the corrected projected
     spanning conclusions on an explicit graph as well; projected spanning is not the blocker on
     that branch either, because the current exact-shell endpoint-bearing upgrade is already
     ruled out above.
     The same benchmark file now pushes one algebraic layer deeper still:
     `exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_atMostOneInteriorEdgePerFace`
     and
     `exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_atMostOneInteriorEdgePerFace`
     show that the explicit live shell also reaches the first chain-dot duality endpoints on the
     natural purified carrier vertex set.  So the remaining burden on that constructive branch is
     not algebraic projection/duality reachability either; the current exact-shell
     endpoint-bearing upgrade is already ruled out above.  The same file now also reaches the raw
     finite corrected Definition 4.8
     representation there:
     `exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_atMostOneInteriorEdgePerFace`
     packages finite Kempe-closure generator sums realizing every class in the corresponding
     boundary-zero Kirchhoff subspace on that same explicit live shell.  So the remaining burden
     on this constructive branch is not raw Definition 4.8 realization either; the current exact-
     shell endpoint-bearing upgrade is already ruled out above.  The same benchmark file now also reaches the
     projected-generator detector there:
     `exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_diamondWithTriangleGraph_for_explicitTaitColoring_via_successorCycle_atMostOneInteriorEdgePerFace`
     shows that every nonzero class in that same boundary-zero Kirchhoff subspace is detected by
     some projected Kempe generator on the explicit live shell.  So the remaining burden on this
     constructive branch is not nontrivial projected-generator detection either; the current exact-
     shell endpoint-bearing upgrade is already ruled out above.
     The same benchmark file now mirrors that projected Definition 4.8 package on the honest
     closed-walk shell too.  The witness
     `exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph`
     packages the fallback/count/boundary-rest surface directly for the cyclic source, and the
     honest-source instantiations
     `exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_diamondWithTriangleGraph_for_explicitTaitColoring_via_closedWalkAtMostOneInteriorEdgePerFace`,
     `exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_diamondWithTriangleGraph_for_explicitTaitColoring_via_closedWalkAtMostOneInteriorEdgePerFace`,
     `exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_diamondWithTriangleGraph_for_explicitTaitColoring_via_closedWalkAtMostOneInteriorEdgePerFace`,
     `exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_diamondWithTriangleGraph_for_explicitTaitColoring_via_closedWalkAtMostOneInteriorEdgePerFace`,
     `exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_diamondWithTriangleGraph_for_explicitTaitColoring_via_closedWalkAtMostOneInteriorEdgePerFace`,
     and
     `exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_diamondWithTriangleGraph_for_explicitTaitColoring_via_closedWalkAtMostOneInteriorEdgePerFace`
     show that the same explicit Tait-colored diamond already reaches the corrected projected
     subspace, spanning, duality, finite realization, and nonzero-detection endpoints without
     passing through successor-cycle packaging.  So the honest closed-walk side is not blocked
     below the current projected nonempty endpoint either; it already reaches the same algebraic
     floor while the exact one-collar projected nonempty upgrade remains refuted above.
     `PlanarBoundaryClosedWalkSourceProjection.lean` now removes most of that remaining
     benchmark-locality too.  The new fixed-embedding source-to-projection bridges
     `projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct`,
     `span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct`,
     `theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct`,
     `theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct`,
     `exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct`,
     and
     `exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_direct`
     show that once an honest cyclic source already carries canonical witness choice, the
     corrected projected subspace, spanning, duality, detector, and finite raw-generator
     endpoints all follow on that very same embedding.  The same file also upgrades the direct
     local at-most-one shell itself to same-embedding theorems:
     `projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct`,
     `span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct`,
     `theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct`,
     `theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct`,
     `exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct`,
     and
     `exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct`.
     So on the honest at-most-one branch the current formal burden is no longer any corrected
     Definition 4.8 algebraic step at all, even at fixed-embedding granularity; the surviving
     obstruction is the projected nonempty carrier endpoint itself.
     The same file now upgrades the honest same-boundary one-collar geometry shell itself to
     same-embedding theorems too:
     `projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct`,
     `span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct`,
     `theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct`,
     `theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct`,
     `exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct`,
     and
     `exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct`.
     So once an honest cyclic source already carries same-boundary one-collar geometry with
     `numCollars = 1`, the corrected projected subspace, spanning, duality, detector, and finite
     raw-generator endpoints already follow on that very same embedding.  The honest one-collar
     geometry branch is therefore not blocked below corrected Definition 4.8 either; the
     surviving burden remains the projected nonempty carrier endpoint and the exact-shell
     upgrades above it.
     The same file now upgrades the route-facing successor-cycle shell with same-boundary
     one-collar geometry to matching fixed-embedding direct theorems:
     `projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct`,
     `span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct`,
     `theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct`,
     `theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct`,
     `exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct`,
     and
     `exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCollarGeometry_with_sourceBoundaryData_direct`.
     So even on the explicit boundary-order presentation, once the shell already carries
     same-boundary one-collar geometry with `numCollars = 1`, the corrected projected subspace,
     spanning, duality, detector, and finite raw-generator endpoints follow on that very same
     embedding.  The route-facing one-collar geometry branch is therefore not blocked below
     corrected Definition 4.8 either; it shares the same surviving projected nonempty carrier
     burden as the honest-source branch.
     The same file now also upgrades the route-facing successor-cycle canonical witness-choice
     shell from existential packaging to matching fixed-embedding direct theorems:
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct`,
     `theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_direct`,
     `projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_direct`,
     `span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_direct`,
     `theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_direct`,
     `theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_direct`,
     `exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_direct`,
     and
     `exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_canonicalWitnessChoice_direct`.
     So once the explicit boundary-order shell already carries canonical witness choice, the
     corrected projected subspace, spanning, duality, detector, and finite raw-generator
     endpoints follow on that very same embedding; if it also has nonempty purified carrier, then
     the positive theorem-4.9 endpoint and raw quotient/error package do too.  The route-facing
     canonical-choice branch is therefore no longer blocked at existential repackaging either; it
     shares the same surviving carrier and exact-shell burdens as the corresponding honest-source
     branch.
     The same file now also upgrades the route-facing successor-cycle local at-most-one shell to
     matching fixed-embedding direct theorems:
     `projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_direct`,
     `span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_direct`,
     `theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_direct`,
     `theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_direct`,
     `exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_direct`,
     and
     `exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace_direct`.
     So on the explicit boundary-order presentation, once the local at-most-one hypotheses are
     already available, the corrected projected subspace, spanning, duality, detector, and finite
     raw-generator endpoints follow on that very same embedding too.  The route-facing at-most-one
     branch is therefore no longer blocked below corrected Definition 4.8 either; it now matches
     the honest-source at-most-one branch in leaving the projected nonempty carrier endpoint as
     the surviving burden.
     `Theorem49AtMostOneNonemptyCarrierImpossibility.lean` now also lifts that impossibility
     diagnosis from the facewise shell to the stronger local-cardinality package itself:
     `not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace`,
     `not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace`,
     `not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace`,
     `not_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_atMostOneInteriorEdgePerFace`,
     and the exact one-collar existential wrappers on both shells.  So the extra fallback-edge
     and boundary-rest data do not rescue this branch either: they only lower it to the corrected
     Definition 4.8 algebraic floor, while the current endpoint witness and projected nonempty
     theorem-4.9 endpoint remain structurally false on that stronger shell.

### Recommendation

Work from `Theorem49PositiveGeometricSourceReplacement.lean` and the source/projection
interfaces rather than trying to inhabit the four refuted package structures.  The next useful
Lean theorem should use the generic cycle-obstruction and selector-compatibility lemmas as the
test for any proposed route-facing boundary-order source: either prove an explicit
selected-boundary break, an injective strict-descent selector with frontier data, or a
well-founded orientation, or instantiate a finite-cycle obstruction showing that the source shell
still leaves the witness-dependency cycle unbroken.
Avoid reviving the at-most-one, canonical-choice, or one-collar/nonempty-carrier branches as
positive endpoints unless the carrier definition or source interface changes.

-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusWitnessRegression
open Theorem49PlanarBoundaryAnnulusHonestGeometryRegression

variable {V : Type*} [DecidableEq V]

/-!
## Status check (2026-04-29: INVESTIGATION COMPLETE - Strategy 2)

**Investigation result**: The original disconnected `counterCollarGeometry` obstruction **does
NOT** carry a honest closed-walk source, but a later connected chained-diamonds model gives the
actual counterexample to honest source plus arbitrary weak collar.

**Finding documented in**: `Theorem49HonestSourceConnectivityInvestigation.lean`

**Key result**: `not_admits_honestSource_counterCollarGeometry` establishes that the
counterexample which violates previous-boundary witness cannot carry honest sources.

**Mechanism**: The underlying `counterGraph` is disconnected (8 disjoint edges with no shared
vertices). Face boundaries span multiple disconnected components, making facial closed walks
impossible.

**Implication**: Connectivity ruled out only the first disconnected obstruction.  It does not
force the repaired witness condition for arbitrary weak collars: the connected chained-diamonds
counterexample shows that the weak collar must be tied to the source boundary split, or the
repaired `WitnessOnCurrentBoundary` condition must be carried explicitly.

## Status check (2026-05-08: residual boundary pass)

`Theorem49ResidualBoundaryPeeling.lean` now adds a residual/current-boundary wrapper around the
existing explicit-remainder collar and boundary-free-selector stacks.  On the positive side, the
wrapper is sufficient to recover
`Theorem49BoundaryRootNonemptyProjectedSynthesis` from already available annulus-collar data via
`theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint_via_residualBoundary`.
So the algebraic backend does not need a new residual proof layer yet; the current residual
surface can lower to the existing theorem-4.9 endpoint.

That conservativity is now exact on the fixed-embedding positive surfaces:
`nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_iff_nonempty_planarBoundaryCollarLayerFacePeelWitnessData`,
`theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn`,
and
`theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_heightOrderedPositiveProjectedGeometryOn`
show that the present residual/current-boundary wrapper adds no new positive geometric strength
beyond the already existing collar-layer / height-ordered packages.
The wheel obstruction now hits that residual shell explicitly:
`not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_wheelWithInnerTriangle` and the failed
universal
`not_forall_theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`
show that honest source data, a real Tait coloring, and a nonempty purified carrier still do not
force residual/current-boundary positive geometry on the same embedding.
The two-collar positive benchmark now calibrates the downstream ceiling on that same residual
surface:
`counterEmbedding_residualBoundaryPositiveProjectedGeometryOn_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData`,
`counterEmbedding_residualBoundaryPositiveProjectedGeometryOn_and_boundaryRootNonemptyProjectedSynthesis_and_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData`,
`counterGraph_explicitTait_residualBoundaryPositiveProjectedGeometry_and_boundaryRootNonemptyProjectedSynthesis_with_forcingInteriorEdgeWitness_without_boundaryFreeSelector_or_planarBoundaryAnnulusConstructionFaceLayerData`,
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_theorem49ResidualBoundaryPositiveProjectedGeometryOn_counterGraph`,
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_theorem49ResidualBoundaryPositiveProjectedGeometryOn_counterGraph`
show that even when the residual wrapper is positively inhabited, and even when that same
embedding already reaches the projected theorem-4.9 endpoint, it still does not force either the
boundary-free selector shell or the annulus-construction face-layer shell.

What this pass now **does** establish is a same-embedding lowering from stronger source-side
canonical-parent cover data.  `Theorem49ResidualBoundaryPeeling.lean` proves
`theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_via_residualBoundary`,
`theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_residualBoundary`,
`theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint`,
`theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary`,
and the corresponding successor-cycle wrappers.  `Theorem49PositiveGeometricSourceReplacementRoute.lean`
and `Theorem49BoundaryFreeSelectorPositiveRoute.lean` supply the same direct lowering to the
generic parent and boundary-free-selector theorem-4.9 endpoints.  So the downstream side of this
stronger source-fixed canonical-parent raw-cover package is now completely explicit: the same
shell already reaches the full theorem-4.9 synthesis endpoint on the same embedding, and the
older `HasUnblockedInteriorEndpoint` hypotheses are needed only for the weaker projected / raw
quotient corollaries.

What the new obstruction pass adds is that this stronger raw-cover shell is no longer merely an
unfinished upstream target on the live endpoint surface.  `Theorem49ForcingInteriorEdgeObstruction.lean`
now proves
`not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover`,
`not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover`,
`not_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover`,
and the matching successor-cycle / graph-level route-shell theorems.  The same raw-cover
hypotheses force `interiorEdgeSupport = ∅`, hence they cannot coexist with either
`HasUnblockedInteriorEndpoint`, the older endpoint-support-disjoint raw carrier shell, or a
nonempty purified selected-boundary carrier on the same embedding.

So the parent, selector, residual, and full-synthesis theorem-4.9 lowerings from the raw
canonical-parent cover package are now calibrated as vacuous on the current live endpoint
semantics.  The remaining live question is no longer how to derive that package together with
`HasUnblockedInteriorEndpoint` from honest source data or from the exact v23 seed.  Even before
any live carrier is added, the same raw-cover shell has already collapsed to the no-interior-edge
branch.  So the route must either change the source interface / endpoint notion or prove
impossibility directly on the live shell.

The obstruction file now ties that gap directly to the exact v23 algebraic seed.
`nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary` builds
`V23ResidualBoundaryInitialState` on an actual shared-interior-pair face boundary, while
`sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_residualBoundaryGeometry`
and
`not_forall_residualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that even this exact Step 2 initial state, together with honest closed-walk source data, a
Tait coloring, and `HasUnblockedInteriorEndpoint`, still does not force any residual positive
geometry on the same embedding.  The stronger theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_residualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair`
and
`not_forall_residualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that this remains false even after adding exact one-collar source-preserving
current-boundary data on the same honest source boundary split.

The same benchmark now already blocks the sharper source-fixed rooted shared-edge
face-membership shell itself.  `Theorem49ResidualBoundaryObstruction.lean`
proves
`not_exists_sharedInteriorPairClosedWalkSourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover`,
so on the shared-interior-pair honest source this concrete rooted-cover package is
impossible outright: it would immediately construct generic
`InteriorDualBoundaryRootAdjDistancePeelData`, contradicting the already formalized
shared-interior-pair IDBRAD obstruction.  This exact-seed obstruction is now known to be
strictly upstream: the new witness theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_sharedInteriorPair`,
together with the matching closed-walk / successor-cycle failed-universal theorems, show that the
same benchmark already refutes any universal derivation of this rooted-cover package from the
honest source or actual successor-cycle shell plus `HasUnblockedInteriorEndpoint`, with no Tait
coloring and no exact `V23ResidualBoundaryInitialState` needed.  The exact-shell witness theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_sharedInteriorPair`,
together with the matching closed-walk / successor-cycle failed-universal theorems,
show that even exact one-collar current-boundary data preserving the honest boundary split still
does not force this sharper rooted-cover package on the live exact shell.  So the repaired exact
shell now fails before the older canonical-parent cover refinements are even reached: the concrete
rooted shared-edge face-membership burden itself is already false on the benchmark.

The same benchmark now also blocks the still-stronger upstream source-fixed
canonical-parent shared-edge face-membership shell.  This obstruction is now
also packaged directly on the seed-free source shells: the new witness theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_sharedInteriorPair`,
together with the matching closed-walk / successor-cycle failed-universal theorems,
show that the honest source and actual successor-cycle shells plus `HasUnblockedInteriorEndpoint`
already do not force this stronger face-membership package, with no Tait coloring and no exact
`V23ResidualBoundaryInitialState` needed.  The theorem
`sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover`
packages the exact Step 2 seed together with failure of that child-membership
refinement on the same honest closed-walk embedding, and
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
shows that no universal theorem of the form “honest source + Tait + endpoint +
exact v23 seed forces some source-fixed canonical-parent face-membership
witness” can hold.  The stronger exact-shell refinement theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_sharedInteriorPair`
and
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that this remains false even after adding exact one-collar current-boundary
data preserving that same honest source boundary split.  `Theorem49ResidualBoundaryObstruction.lean`
now upgrades both exact-shell failures to generic converse theorems:
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`.
So any same-embedding honest-source exact-shell witness with `HasUnblockedInteriorEndpoint`
already refutes a universal derivation of that stricter face-membership shell; the
shared-interior-pair benchmark is just one instantiation.

The same benchmark now also blocks the stronger upstream source-fixed raw-cover shell itself.
This obstruction is now also packaged directly on the seed-free source shells: the new witness
theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_sharedInteriorPair`,
together with the matching closed-walk / successor-cycle failed-universal theorems, show that the
honest source and actual successor-cycle shells plus `HasUnblockedInteriorEndpoint` already do not
force this raw canonical-parent cover package, with no Tait coloring and no exact
`V23ResidualBoundaryInitialState` needed.
`sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover`
packages the exact Step 2 seed together with failure of the closed-walk raw canonical-parent
shared-edge-cover package on that same embedding, and
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
shows that no universal theorem of the form “honest source + Tait + endpoint + exact v23 seed
forces some source-fixed raw canonical-parent cover witness” can hold.  The stronger exact-shell
refinement theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_sharedInteriorPair`
and
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that this remains false even after adding exact one-collar current-boundary data preserving
that same honest source boundary split.  `Theorem49ResidualBoundaryObstruction.lean` now also
upgrades both exact-shell failures to generic converse theorems:
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`.
So any same-embedding honest-source exact-shell witness with `HasUnblockedInteriorEndpoint`
already refutes a universal derivation of that raw canonical-parent shell; the shared-interior-pair
benchmark is just one instantiation.

The same exact seed now fails even to recover the weaker degenerate branch to which that raw-cover
shell collapses.  This obstruction is now also packaged directly on the seed-free source shells:
the new witness theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsNoInteriorEdges_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsNoInteriorEdges_sharedInteriorPair`,
together with the matching closed-walk / successor-cycle failed-universal theorems, show that the
honest source and actual successor-cycle shells plus `HasUnblockedInteriorEndpoint` already do not
force even this degenerate branch, with no Tait coloring and no exact
`V23ResidualBoundaryInitialState` needed.  The theorem
`sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsNoInteriorEdges`
packages the exact Step 2 seed together with failure of the closed-walk root-cover plus
`interiorEdgeSupport = ∅` shell itself, and
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
shows that no universal theorem of the form “honest source + Tait + endpoint + exact v23 seed
forces some no-interior-edge boundary-root witness” can hold either.  The matching exact-shell
refinement theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsNoInteriorEdges_sharedInteriorPair`
and
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that exact one-collar current-boundary data still does not recover even that degenerate
source-fixed no-interior-edge branch.

The same exact seed also fails already at the strictly weaker local boundary-free-selector
surface.  This obstruction is now also packaged directly on the seed-free source shells: the new
witness theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint_without_boundaryFreeIncidentFaceSelector_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint_without_boundaryFreeIncidentFaceSelector_sharedInteriorPair`,
together with the matching closed-walk / successor-cycle failed-universal theorems, show that the
honest source and actual successor-cycle shells plus `HasUnblockedInteriorEndpoint` already do not
force even a boundary-free selector, with no Tait coloring and no exact
`V23ResidualBoundaryInitialState` needed.  The theorem
`sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector`
packages the exact Step 2 seed together with failure of
`BoundaryFreeIncidentFaceSelector` on the same honest embedding, and
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
shows that no universal theorem of the form “honest source + Tait + endpoint + exact v23 seed
forces a boundary-free selector” can hold either.  So the exact seed does not even recover the
local no-forcing surface that any selector/construction descent route would need before source
packaging questions arise.

The same calibration now reaches the actual route-facing boundary-order shell:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_residualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair`
and
`not_forall_residualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that successor-cycle source data plus selected-boundary arcs, the exact v23 seed, a Tait
coloring, and `HasUnblockedInteriorEndpoint` still do not force residual positive geometry.  The
parallel exact-shell theorems
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_residualBoundaryPositiveProjectedGeometryOn_sharedInteriorPair`
and
`not_forall_residualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that even exact one-collar current-boundary data preserving the extracted boundary split
still adds no forcing at the actual boundary-order source surface.
The same route-facing shell already fails at the stricter child-membership
face-membership refinement too:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_sharedInteriorPair`
and
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that successor-cycle boundary-order data plus the exact v23 seed still do
not force even that stronger canonical-parent face-membership shell on the same
embedding.  The parallel exact-shell theorems
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_sharedInteriorPair`
and
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that exact one-collar current-boundary data preserving the selected
boundary split still adds no forcing even at that stronger route-facing
surface.  The same file now lifts these to generic exact-shell converse failures:
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`.
So any same-embedding successor-cycle exact-shell witness with `HasUnblockedInteriorEndpoint`
already refutes a universal derivation of that stronger route-facing face-membership shell.
The stronger route-facing raw-cover shell is now blocked too:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_sharedInteriorPair`
and
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that successor-cycle boundary-order data plus the exact v23 seed still do not force even the
raw canonical-parent shared-edge-cover shell on the same embedding.  The parallel exact-shell
theorems
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_sharedInteriorPair`
and
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that exact one-collar current-boundary data preserving the selected boundary split still adds
no forcing at that stronger route-facing raw-cover surface either.  The same file now lifts these
to generic exact-shell converse failures:
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`.
So any same-embedding successor-cycle exact-shell witness with `HasUnblockedInteriorEndpoint`
already refutes a universal derivation of that route-facing raw-cover shell.

The same successor-cycle shell also fails already at the weaker degenerate source branch:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsNoInteriorEdges_sharedInteriorPair`
and
`not_forall_some_successorCycleBoundaryFaceRootsNoInteriorEdges_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that the exact seed does not even force the route-facing boundary-root plus
`interiorEdgeSupport = ∅` shell on the same embedding.  The matching one-collar refinement theorems
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsNoInteriorEdges_sharedInteriorPair`
and
`not_forall_some_successorCycleBoundaryFaceRootsNoInteriorEdges_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that even exact one-collar current-boundary data still does not force that weaker route-facing
degenerate branch.

The same successor-cycle shell also fails already at the weaker selector layer:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_sharedInteriorPair`
and
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that the exact seed does not even force a route-facing boundary-free selector on the same
embedding.

The same exact v23 seed also fails to repair any previously known same-embedding witness route.
`sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_knownSameEmbeddingGeometry`
packages the honest source, Tait coloring, endpoint witness, and exact seed together with failure
of residual witness data, residual selector data, height-ordered witness data, collar-layer
witness data, the attached boundary-rooted certificate, well-founded witness data, and weak
annulus-collar geometry on the same embedding.  The stronger exact-shell theorem
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_knownSameEmbeddingGeometry_sharedInteriorPair`
shows that even exact one-collar source-preserving current-boundary data does not repair any of
those known same-embedding ladders on the honest source shell.  More sharply, the theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair`
already isolate the route-facing weak annulus-collar geometry shell itself: even that single
same-embedding geometric burden is not forced by the exact one-collar plus exact-v23 shell.  The
same exact shell now also fails at the central acyclic witness burden itself: the theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair`
show that even same-embedding well-founded parent-peeling is not recovered on either exact-shell
source surface.  The
failed universals
`not_forall_some_knownSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
and
`not_forall_some_knownSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`,
`not_forall_some_knownSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`,
and
`not_forall_some_knownSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that this gap already persists on both the honest closed-walk and the actual successor-cycle
boundary-order shells, even after adding exact one-collar current-boundary data preserving the
same extracted annulus boundary split.  The same exact-shell diagnosis now also lifts to generic
converse theorems:
`not_forall_some_knownSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_some_knownSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`.
So any explicit same-embedding exact-shell witness carrying simultaneous failure of the currently
known geometry surfaces already refutes a universal derivation of that whole disjunctive burden;
the shared-interior-pair shell is just one concrete instantiation.  So the missing v23.5 theorem
is not a way to re-enter
one of the older same-embedding geometry ladders, or even to recover the upstream raw-cover
shell, from the exact Step~2 algebraic seed, or even its boundary-free-selector / degenerate
no-interior-edge shadows; it is a genuinely new source-to-residual geometric bridge or
live-boundary cancellation certificate.

The same exact one-collar plus exact-v23 shell still does not even recover the current direct or
route-facing replacement-positive packages.  The theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair`,
together with the failed universals
`not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
and
`not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`,
show that even exact one-collar current-boundary data preserving the same extracted annulus
boundary split still does not recover the direct or route-facing replacement-positive endpoints
from the exact Step~2 seed.  The same exact-shell obstruction now also lifts to generic converse
theorems:
`not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`.
So any explicit same-embedding exact-shell witness carrying simultaneous failure of the current
direct and route-facing replacement-positive endpoints already refutes a universal derivation of
that whole positive disjunction; the shared-interior-pair shell is again just one concrete
instantiation.  The same shared-interior-pair successor-cycle shell is now also packaged directly
with the local two-interior-edge burden at that replacement-positive boundary:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair`
shows that the exact one-collar/v23 benchmark already carries a concrete face boundary with two
distinct interior edges while still failing every current direct and route-facing
replacement-positive package on that same embedding.

The same exact one-collar plus exact-v23 shell also still does not recover even the downstream
positive construction face-layer shell.  The theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair`,
together with the failed universals
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`,
show that even exact one-collar current-boundary data preserving the same extracted annulus
boundary split still does not force `PlanarBoundaryAnnulusConstructionFaceLayerData` from the
exact Step~2 seed.  Since the current selected-boundary, face-partition, and positive-frontier
construction shells all lower to the face-layer shell, this exact-shell gap already blocks the
whole positive construction stack.  The same exact-shell obstruction now also lifts to generic
forcing-edge converse theorems:
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness`
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness`.
So any explicit same-embedding exact-shell witness carrying a forcing interior edge already
refutes a universal derivation of `PlanarBoundaryAnnulusConstructionFaceLayerData` from that
shell; the shared-interior-pair benchmark is only one concrete instantiation.  The same file now
also states the repaired local burden on
that exact shell itself:
`not_forall_not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
and
`not_forall_not_nonempty_forcingInteriorEdgeWitness_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that even this exact one-collar v23/v23.5 source package still does not universally exclude
forcing interior edges.  So any sound repair on that shell must add or derive a precise local
no-forcing hypothesis before it can hope to reach the downstream face-layer package.

At the same time, the exact Step~2 seed is not globally incompatible with the degenerate
source-fixed no-interior branch.  The new module
`Theorem49ResidualBoundaryPositiveRegression.lean` equips the existing two-triangle no-interior
source with a proper nonzero Tait edge coloring `twoTriangleTaitEdgeColoring`, proves
`nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState`, and then packages the same exact
seed together with the honest closed-walk source, the root-cover / root-separation facts, empty
`interiorEdgeSupport`, the resulting
`InteriorDualBoundaryRootParentPeelData`, and even a
`BoundaryFreeIncidentFaceSelector` on that embedding.  The new coexistence theorems
`twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis`
and
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis`
now make that selector compatibility explicit on both the honest closed-walk shell and the live
successor-cycle shell.  The stronger coexistence theorems
`twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells`
and
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells`
now show that even this selector compatibility still coexists with failure of every currently
formalized positive-stage construction shell on both source interfaces.  In fact the same
concrete benchmark now already reaches full theorem-4.9 synthesis on that no-interior parent
branch:
`theorem49BoundaryRootSynthesis_twoTriangleAnnulusEmbedding_for_explicitTaitColoring_via_noInteriorParentRoute`
proves the endpoint on the actual embedding, and
`twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis`
plus
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis`
package the same coexistence on the honest closed-walk and live successor-cycle shells.
So the shared-interior-pair exact-seed obstructions are not exposing an outright incompatibility
between v23 Step~2 algebra and the degenerate no-interior source surfaces; they isolate a genuine
non-forcing gap on the live endpoint benchmark.

The repaired positive direction is now stated on the exact shell itself in
`Theorem49ResidualBoundaryRoute.lean`.
`theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint`
and
`theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint`
say exactly what the current strongest sound v23/v23.5 repair is: if the exact one-collar shell
already carries annulus-root parent peel data on the same annulus boundary split, then the local
endpoint witness closes the route all the way to
`Theorem49BoundaryRootNonemptyProjectedSynthesis`.  So the remaining geometric burden is no
longer ambiguous: it is to produce that same-split parent-peel certificate, not another
projection or symmetry wrapper.

The constructive selector/construction lane now advances one real shell further in
`Theorem49BoundaryFreeSelectorConstruction.lean`.
`planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary`
and its successor-cycle counterpart
`planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary`
show that same-split annulus-root parent peel data already lowers to the real
`PlanarBoundaryAnnulusConstructionBoundarySupportFaceData` shell once the exact local gap is
discharged: peeled faces missed by the selector image must still touch selected-boundary support,
and the resulting positive `currentOuterBoundary` layers must be nonempty and pairwise disjoint.
So the missing parent-peel-to-construction step is now stated honestly and sharply.  It is not a
generic non-peeled-face burden on all ambient faces, but the strictly smaller selector-deficit
peeled-face condition.
The same exact one-collar/v23 shell now also has generic forcing-edge converse failures already at
that stronger construction surface and the next two intermediate construction shells:
`not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness`
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness`.
`not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness`,
`not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness`,
`not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness`,
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness`
now show the same thing one layer later inside the construction lane.
So any explicit same-embedding exact-shell witness carrying a forcing interior edge already
refutes universal derivations of `PlanarBoundaryAnnulusConstructionBoundarySupportFaceData`,
`PlanarBoundaryAnnulusConstructionFacePartitionData`, and
`PlanarBoundaryAnnulusConstructionPositiveFrontierData`; the live gap therefore persists before
the final lowering to face-layer data.
The same shared-interior-pair successor-cycle shell is now also packaged directly at that
positive-frontier boundary:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionPositiveFrontierData_sharedInteriorPair`
shows that the exact one-collar/v23 benchmark already carries a concrete face boundary with two
distinct interior edges while still failing `PlanarBoundaryAnnulusConstructionPositiveFrontierData`
on that same embedding.
The same shared-interior-pair successor-cycle shell is now also packaged directly with the local
two-interior-edge burden at that face-layer boundary:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData_sharedInteriorPair`
shows that the exact one-collar/v23 benchmark already carries a concrete face boundary with two
distinct interior edges while still failing `PlanarBoundaryAnnulusConstructionFaceLayerData` on
that same embedding.

That same repaired exact-shell package now reaches the downstream construction face-layer shell
used by annulus decomposition.  `Theorem49ResidualBoundaryRoute.lean` proves
`nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary`
and
`nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary`.
So once the exact one-collar shell carries same-split parent peel data together with the
selector-deficit selected-boundary condition and the positive `currentOuterBoundary` side
conditions, the route no longer stops at selected-boundary support data: it already produces real
`PlanarBoundaryAnnulusConstructionFaceLayerData` on that same embedding.  The live burden is
therefore even sharper than before: derive this exact repaired local package from the residual
shell, not some additional face-layer or decomposition wrapper.

That same repaired exact-shell package now also reaches a real annulus decomposition on the same
embedding.  `Theorem49ResidualBoundaryRoute.lean` proves
`nonempty_planarBoundaryAnnulusDecomposition_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary`
and
`nonempty_planarBoundaryAnnulusDecomposition_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary`.
So once the exact shell carries the same-split parent-peel and selector-deficit package, the
route already passes through annulus decomposition itself.  The remaining burden is therefore not
another decomposition-side shell, but whatever stronger geometry or witness data is needed
downstream of that repaired local package.

That same repaired exact-shell package now also has an honest full synthesis endpoint once the
exact construction induced by that package carries witness ownership.  `Theorem49ResidualBoundaryRoute.lean` proves
`theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_inducedDecompositionWitnessAssignment`,
`theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_inducedDecompositionWitnessAssignment`,
and also the older chosen-decomposition forms
`theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_resultingDecompositionWitnessAssignment`
and
`theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_resultingDecompositionWitnessAssignment`.
So once the exact shell carries the same-split parent-peel and selector-deficit package, no
further theorem-4.9 algebra remains after the derived decomposition acquires witness ownership.
More sharply, the live downstream burden is now to build
`PlanarBoundaryAnnulusWitnessAssignment` on the exact same-embedding annulus decomposition
canonically induced by that repaired parent-peel construction, rather than on an arbitrary chosen
decomposition or through another selector wrapper.

That same repaired local package now already discharges the forcing-edge obstruction on the exact
one-collar v23/v23.5 shell itself.  `Theorem49ResidualBoundaryRoute.lean` proves
`not_nonempty_forcingInteriorEdgeWitness_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary`
and
`not_nonempty_forcingInteriorEdgeWitness_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary`.
So once the exact shell carries same-split parent peel data together with the selector-deficit
selected-boundary hypothesis and the positive `currentOuterBoundary` conditions, forcing interior
edges are excluded on that same embedding.  The remaining exact-shell burden is therefore no
longer an unspecified no-forcing theorem, but precisely to derive this explicit selector-deficit
construction package from the actual residual shell.
The same file now also records that this burden can be stated one layer more directly on the
actual boundary-order selector package itself:
`not_nonempty_forcingInteriorEdgeWitness_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions`
and
`theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions_and_inducedDecompositionWitnessAssignment`.
The same route is now also named directly on the actual successor-cycle shell by
`not_nonempty_forcingInteriorEdgeWitness_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions`,
`theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions_and_inducedDecompositionWitnessAssignment`,
and the graph-level closure
`exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFreeIncidentFaceSelector_and_boundarySupportFaceData_conditions_and_inducedDecompositionWitnessAssignment_direct`.
So once boundary reachability together with facewise selected-boundary arcs already supports a
boundary-free selector whose nonselected faces meet selected-boundary support and whose induced
positive `currentOuterBoundary` layers are nonempty and pairwise disjoint, both the forcing-edge
obstruction and the remaining theorem-4.9 algebra disappear on that same embedding.  More
sharply, the remaining burden is witness ownership on the exact selector-induced annulus
decomposition, not merely on an unspecified chosen decomposition.  The live exact-shell burden is
therefore better stated directly at this selector-side local package, and then at that induced
decomposition, rather than at another intermediate construction shell; and once that exact
successor-cycle selector package is available at graph level, no further route-level repackaging
step remains before full `Theorem49BoundaryRootSynthesis`.

The same positive exact-seed benchmark now also shows where that compatibility stops on the
construction side.  `Theorem49ResidualBoundaryPositiveRegression.lean` still proves
`nonempty_twoTriangleClosedWalkSourcePlanarBoundaryAnnulusConstruction` and the actual
successor-cycle package
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_planarBoundaryAnnulusConstruction`,
but it also proves
`not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_twoTriangleAnnulusEmbedding`,
`not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_twoTriangleAnnulusEmbedding`,
`not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_twoTriangleAnnulusEmbedding`,
and
`not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_twoTriangleAnnulusEmbedding`.
So the exact Step~2 seed is compatible with the degenerate no-interior branch up through the base
annulus construction and residual witness surfaces, and indeed even through full
`Theorem49BoundaryRootSynthesis` on the same embedding via the no-interior parent route, yet it
still cannot supply any genuinely positive-stage frontier package there: every positive
`currentOuterBoundary` is forced inside `interiorEdgeSupport = ∅`.  More sharply, this is now
stated directly as a synthesis-side failed converse on that benchmark:
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData`
packages the live successor-cycle shell together with the exact Step~2 seed, full
`Theorem49BoundaryRootSynthesis`, and failure of positive-frontier data on one embedding; then
`SomePositiveStageConstructionShell`,
`NoPositiveStageConstructionShells`,
`not_somePositiveStageConstructionShell_of_noPositiveStageConstructionShells`,
and
`noPositiveStageConstructionShells_of_interiorEdgeSupport_eq_empty` in
`PlanarBoundaryAnnulusConstructionCore.lean`,
as well as
`noPositiveStageConstructionShells_twoTriangleAnnulusEmbedding`,
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells`,
and
`exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells_twoTriangleAnnulusGraph`
show that this is not an isolated last-shell defect: on the actual successor-cycle benchmark,
full theorem-4.9 synthesis already coexists with simultaneous failure of all four currently
formalized positive-stage construction shells at once, namely boundary-support face data,
face-partition data, face-layer data, and positive-frontier data.  The separate witness theorems
`exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionPositiveFrontierData_twoTriangleAnnulusGraph`
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph`
show that even the final theorem-4.9 endpoint under a real Tait coloring does not universally
force the positive-frontier construction shell.  This is now also lifted to a reusable
witness-based converse in `Theorem49Synthesis.lean`:
`not_forall_nonempty_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without`
abstracts the witness-to-failed-universal pattern itself, while
`not_forall_somePositiveStageConstructionShell_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells`
packages the whole disjunctive positive-stage surface at once, and
`not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionBoundarySupportFaceData`,
`not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionFacePartitionData`,
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionFaceLayerData`,
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusConstructionPositiveFrontierData`
says any same-embedding example carrying a Tait coloring, full theorem-4.9 synthesis, and
failure of one of those positive-stage construction packages already refutes the corresponding
universal implication.  `Theorem49ResidualBoundaryPositiveRegression.lean` now instantiates the
same reusable converse pattern for the exact two-triangle benchmark not only at
positive-frontier data but also at boundary-support face data, face-partition data, and the
stronger face-layer shell, and at the single aggregated disjunctive
`SomePositiveStageConstructionShell` surface.  It now also pushes that same failed-converse
diagnosis back up to the actual exact-v23 source shells themselves:
`twoTriangle_closedWalkSource_tait_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells`,
`exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_somePositiveStageConstructionShell_twoTriangleAnnulusGraph`,
and
`not_forall_somePositiveStageConstructionShell_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph`
do this on the honest closed-walk shell, while
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_somePositiveStageConstructionShell_twoTriangleAnnulusGraph`
and
`not_forall_somePositiveStageConstructionShell_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph`
do the same on the live successor-cycle selected-arc shell.  Those route-facing failed
universals are now no longer benchmark-local proof scripts: `Theorem49ResidualBoundaryRoute.lean`
also packages the reusable exact-v23 source-shell converses
`not_forall_somePositiveStageConstructionShell_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells`
and
`not_forall_somePositiveStageConstructionShell_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells`,
and the two-triangle source-shell failures now instantiate those shell-specific exact-v23 route
helpers directly from the stronger witness package `NoPositiveStageConstructionShells`.
The same route file now also pushes that converse architecture one step closer to the repaired
live shell by adding the exact one-collar current-boundary versions
`not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_target`,
`not_forall_target_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_without_target`,
`not_forall_somePositiveStageConstructionShell_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells`,
and
`not_forall_somePositiveStageConstructionShell_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells`.
So once a future benchmark carries theorem-4.9 synthesis and a real exact one-collar residual
shell on the same embedding, the failed-converse layer no longer needs benchmark-local proof
scripts.  The positive two-triangle benchmark now also supplies one concrete inhabitant of that
exact-shell witness side below theorem-4.9 itself:
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData`
shows that the live successor-cycle exact one-collar/v23 shell already reaches a real
`PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData` witness on the same embedding.
The strengthening
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData`
adds the full theorem-4.9 synthesis endpoint to that same exact shell.
The new blocker theorem
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn`
then records exactly why this still does not inhabit the next positive route lane: on the same
embedding the interior-edge support is empty, so
`not_hasUnblockedInteriorEndpoint_twoTriangleAnnulusEmbedding`,
`not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_twoTriangleAnnulusEmbedding`,
`not_theorem49ResidualBoundaryPositiveProjectedGeometryOn_twoTriangle`,
`not_theorem49CollarLayerPositiveProjectedGeometryOn_twoTriangle`, and
`not_theorem49HeightOrderedPositiveProjectedGeometryOn_twoTriangle`
all hold simultaneously.  So the two-triangle exact shell is now a Lean-visible positive
benchmark plus blocker, rather than merely an isolated residual witness.
The still-stronger package
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn`
shows that this blocker survives even after adjoining theorem-4.9 synthesis itself to the same
exact one-collar residual witness shell.
`Theorem49ResidualBoundaryPositiveRegression.lean` now also lifts both benchmark-local blockers
to reusable failed-converse theorems:
`not_forall_any_positiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_twoTriangle`
and
`not_forall_any_positiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_twoTriangle`.
So the two-triangle exact-v23 no-interior shell is no longer only a positive benchmark plus local
blocker; it now formally refutes any universal derivation from that exact successor-cycle
current-boundary shell, with residual-boundary layer witness data and even after full
`Theorem49BoundaryRootSynthesis`, to any of the current residual / collar-layer /
height-ordered positive projected-geometry targets.
That diagnosis is now also lifted to reusable witness-based converses:
`not_forall_any_positiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData`
and
`not_forall_any_positiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData`.
So once any graph-level exact one-collar/v23 successor-cycle shell carries a same-embedding
residual-boundary layer witness and still fails those direct positive endpoints, the corresponding
universal converse is already refuted without replaying the two-triangle benchmark proof.
The same file now also lifts the route-facing replacement-positive obstruction on that shell:
`not_theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_twoTriangle`,
`not_theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn_twoTriangle`,
the bundled blockers
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn`
and
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn`,
and the failed universals
`not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_twoTriangle`
and
`not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_twoTriangle`.
So even after adjoining exact one-collar current-boundary data, the exact v23 seed,
same-embedding residual-boundary layer witness data, and full theorem-4.9 synthesis, the
two-triangle successor-cycle shell still does not force any of the current replacement-positive
targets either, including the route-facing honest closed-walk and successor-cycle annulus-collar
packages.
The same replacement-positive diagnosis is now also available in reusable witness-based form:
`not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData`
and
`not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData`.
So the exact-v23 residual-layer obstruction is no longer tied to the concrete two-triangle graph:
any graph-level witness of that same shell, together with same-embedding failure of the current
direct and route-facing replacement-positive endpoints, already collapses the universal converse.
That live-shell diagnosis is now also exhibited by concrete graph-level successor-cycle witness
packages themselves:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn_twoTriangleAnnulusGraph`,
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn_twoTriangleAnnulusGraph`,
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn_twoTriangleAnnulusGraph`,
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn_twoTriangleAnnulusGraph`.
So the same two-triangle graph now witnesses that exact one-collar/v23 residual-layer
obstruction not only on the fixed `twoTriangleAnnulusEmbedding`, but as a graph-level existential
package directly on the live successor-cycle selected-arc shell too.
The same successor-cycle exact-shell branch is now also blocked at the projected nonempty
theorem-4.9 endpoint itself, not only at the positive geometry packages above.
`not_theorem49BoundaryRootNonemptyProjectedSynthesis_twoTriangle` records the fixed-embedding
carrier obstruction; the bundled benchmark theorem
`twoTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_theorem49BoundaryRootNonemptyProjectedSynthesis`
shows that exact one-collar current-boundary data, the exact v23 seed, a same-embedding
residual-boundary layer witness, and full `Theorem49BoundaryRootSynthesis` already coexist on the
live successor-cycle shell while `Theorem49BoundaryRootNonemptyProjectedSynthesis` still fails.
This now comes both as a benchmark-local failed universal
`not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_twoTriangle`
and as graph-level witness/converse packaging:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_theorem49BoundaryRootNonemptyProjectedSynthesis_twoTriangleAnnulusGraph`
and
`not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData`.
So even after theorem-4.9 synthesis itself already closes on that exact residual-layer shell,
the live successor-cycle source does not yet force the nonvacuous projected endpoint.
The same exact-v23 residual-layer diagnosis now also exists on the honest closed-walk source
presentation.  The witness packages
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn_twoTriangleAnnulusGraph`,
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_positiveProjectedGeometryOn_twoTriangleAnnulusGraph`,
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn_twoTriangleAnnulusGraph`,
and
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_any_replacementPositiveProjectedGeometryOn_twoTriangleAnnulusGraph`
show that the same two-triangle exact one-collar/v23 residual witness shell already fails the
direct and route-facing positive endpoints on the honest source too.  The corresponding reusable
converses
`not_forall_any_positiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData`,
`not_forall_any_positiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData`,
`not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_nonempty_residualBoundaryLayerFacePeelWitnessData`,
and
`not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData`
put the same failed-converse diagnosis on both exact-v23 one-collar source presentations.
The honest closed-walk exact-v23 residual-layer shell is now also blocked at the projected
nonempty theorem-4.9 endpoint itself.  The fixed-embedding benchmark theorem
`twoTriangle_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_theorem49BoundaryRootNonemptyProjectedSynthesis`
shows that exact one-collar current-boundary data, the exact v23 seed, a same-embedding
residual-boundary layer witness, and full `Theorem49BoundaryRootSynthesis` already coexist on the
honest closed-walk shell while `Theorem49BoundaryRootNonemptyProjectedSynthesis` still fails.
This now comes both as a benchmark-local failed universal
`not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_twoTriangle`
and as graph-level witness/converse packaging:
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData_without_theorem49BoundaryRootNonemptyProjectedSynthesis_twoTriangleAnnulusGraph`
and
`not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_theorem49BoundaryRootSynthesis_and_nonempty_residualBoundaryLayerFacePeelWitnessData`.
So even after theorem-4.9 synthesis itself already closes on that exact residual-layer shell,
the honest closed-walk source does not yet force the nonvacuous projected endpoint either.
The same exact-v23 source-shell diagnosis is now also stated after adding an explicit local
selector.  The two-triangle benchmark theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_without_somePositiveStageConstructionShell_twoTriangleAnnulusGraph`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_without_somePositiveStageConstructionShell_twoTriangleAnnulusGraph`,
together with the failed universals
`not_forall_somePositiveStageConstructionShell_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph`
and
`not_forall_somePositiveStageConstructionShell_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_twoTriangleAnnulusGraph`,
show that even exact-v23 source shells carrying a real `BoundaryFreeIncidentFaceSelector` and the
full theorem-4.9 endpoint still do not force any currently formalized positive-stage
construction shell.  `Theorem49ResidualBoundaryRoute.lean` now packages the corresponding
reusable selector-strengthened exact-v23 route converses
`not_forall_somePositiveStageConstructionShell_of_exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells`
and
`not_forall_somePositiveStageConstructionShell_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_boundaryFreeIncidentFaceSelector_and_theorem49BoundaryRootSynthesis_and_noPositiveStageConstructionShells`.
So on this degenerate branch the live gap is now calibrated even more sharply: it begins strictly
after the selector layer and remains open even after full theorem-4.9 synthesis is already in
hand on the same exact-v23 source shells.

The same exact Step~2 seed is now also calibrated on a live nondegenerate carrier benchmark.
`Theorem49ForcingInteriorEdgeObstructionRegression.lean` proves
`nonempty_wheelWithInnerTriangle_v23ResidualBoundaryInitialState_wheelFace0Boundary` and then
packages that exact seed together with the honest closed-walk source, the concrete wheel Tait
coloring, and the nonempty purified selected-boundary interior carrier in
`wheelWithInnerTriangle_closedWalkSource_tait_nonempty_carrier_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry`.
On that same wheel embedding, the residual boundary layer witness data, residual selector data,
height-ordered witness data, and collar-layer witness data all still fail.  The same file now
also defines the actual successor-cycle boundary-order geometry
`wheelWithInnerTriangleDartSuccessorCycleGeometry` with
`wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace`, and packages the
exact seed on that route-facing shell in
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_wheelWithInnerTriangle`.
The failed universals
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_wheelWithInnerTriangle`
and
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_wheelWithInnerTriangle`
show that neither honest closed-walk source data nor actual successor-cycle boundary-order data,
even together with a Tait coloring, a live purified carrier, and the exact v23 seed, forces any
of the current residual same-embedding witness packages on the nondegenerate wheel benchmark.
The stronger exact-shell theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_wheelWithInnerTriangle`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_wheelWithInnerTriangle`,
together with the failed universals
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_wheelWithInnerTriangle`
and
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_wheelWithInnerTriangle`,
show that even exact one-collar current-boundary data preserving the extracted annulus boundary
split still adds no forcing on this live nondegenerate carrier benchmark.  So the exact seed is
now calibrated on both sides: it is compatible with the degenerate no-interior branch, but it
also remains non-forcing on a live nondegenerate carrier source all the way up to the actual
boundary-order shell, even after the exact one-collar refinement.  The same wheel natural
residual obstruction is now lifted to the reusable converses
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`
and
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`,
so both the honest closed-walk and successor-cycle exact-shell natural residual obstructions are
now available in reusable witness-based form.  Any same-embedding exact one-collar/v23 example
with a real Tait coloring, nonempty purified carrier, and nonempty
`V23ResidualBoundaryInitialState`, but without any of the current natural residual
same-embedding endpoints, already refutes any universal derivation of that natural residual
burden.
The same file now also shows that adjoining a real local endpoint witness does not rescue that
exact-shell natural residual lane either.  It proves the endpoint-bearing witnesses
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_wheelWithInnerTriangle`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_wheelWithInnerTriangle`,
their failed universals
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`
and
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`,
and the reusable converses
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`.
So even on the endpoint-bearing exact-v23 one-collar honest closed-walk and successor-cycle
shells, a real Tait coloring plus `HasUnblockedInteriorEndpoint` still does not force any
current natural residual same-embedding witness package.
The same file now also packages that exact-shell residual obstruction against the graph-level
theorem-4.9 endpoint itself:
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_naturalResidualSameEmbeddingGeometry`
shows that the explicit Tait coloring still has a graph-level synthesis witness on some
embedding even while the honest exact-v23 successor-cycle one-collar wheel shell with the same
coloring and a live purified carrier still lacks residual boundary witness data, residual
selector data, height-ordered witness data, and collar-layer witness data on the fixed wheel
embedding.
The same benchmark now also carries its local forcing burden on that exact theorem-4.9-adjoined
wheel shell:
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_naturalResidualSameEmbeddingGeometry`
adds a concrete face boundary with two distinct interior edges to the same successor-cycle
package, and the new honest-source graph-level companion
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_naturalResidualSameEmbeddingGeometry`
does the same on the closed-walk shell.  So this nondegenerate wheel obstruction is now visible
not only as a witness-package failure on the fixed exact-v23 shell, but already as a
witness-package failure coexisting with the local two-interior-edge face burden on both source
presentations of that same shell.
The same file now pushes that exact-v23 one-collar wheel benchmark one layer higher, to the
direct and route-facing replacement-positive surface.  The theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn_wheelWithInnerTriangle`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn_wheelWithInnerTriangle`,
together with the failed universals
`not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`
and
`not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`,
show that even exact one-collar current-boundary data, together with a real Tait coloring, a
live purified carrier, and the exact v23 residual seed, still does not force either direct
replacement-positive package or the route-facing annulus-collar replacement packages on the
nondegenerate wheel benchmark.  The same file now also records the local obstruction directly on
that successor-cycle exact-v23 shell:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_replacementPositiveProjectedGeometryOn_wheelWithInnerTriangle`
shows that the same fixed wheel shell already carries a concrete face boundary with two distinct
interior edges while still failing every current direct and route-facing replacement-positive
package.  So this upstream positive obstruction is now visible directly at the benchmark
geometry itself, not only through the downstream failed universal.  The same exact-shell
replacement-positive wheel obstruction is now also lifted to the reusable converses
`not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`
and
`not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`,
so both the honest closed-walk and successor-cycle exact-shell
replacement-positive obstructions are now available in reusable witness-based form.  Any
same-embedding exact one-collar/v23 witness with a real Tait coloring, nonempty purified
carrier, and nonempty `V23ResidualBoundaryInitialState`, but without one of the current direct
or route-facing replacement-positive endpoints, already refutes a universal derivation of that
whole positive burden.
The same file now also pushes that exact-v23 one-collar wheel shell down to the positive
construction face-layer package.  The theorems
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle`,
together with the failed universals
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`,
show that even this stronger live benchmark still does not force the downstream positive
construction face-layer package on either the honest closed-walk or successor-cycle shell.  The
same wheel face-layer obstruction is now lifted to the reusable converses
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`,
so both the honest closed-walk and successor-cycle exact-shell face-layer obstructions are now
available in reusable witness-based form.  Any same-embedding exact one-collar/v23 example with
a real Tait coloring, nonempty purified carrier, and nonempty `V23ResidualBoundaryInitialState`,
but without construction face-layer data, already refutes a universal derivation of that
downstream positive face-layer burden.  The
same file also now records the local obstruction directly on that successor-cycle exact-v23
shell:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle`
shows that the same fixed wheel shell already carries a concrete face boundary with two distinct
interior edges while still failing the upstream face-layer package.  So the wheel obstruction is
now visible directly at the benchmark geometry itself, not only through the downstream failed
universal.  The
same file now also packages that face-layer obstruction against the graph-level theorem-4.9
endpoint itself:
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_planarBoundaryAnnulusConstructionFaceLayerData`
shows that the explicit Tait coloring still has a graph-level synthesis witness on some
embedding even while the honest exact-v23 successor-cycle one-collar wheel shell fails the
same-embedding positive construction face-layer package.
The same file now also shows that this exact-v23 one-collar wheel shell still does not force any
same-embedding annulus decomposition with witness ownership.  The fixed-embedding theorem
`not_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_wheelWithInnerTriangle`, the
honest closed-walk exact-shell package
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_any_planarBoundaryAnnulusWitnessAssignment_wheelWithInnerTriangle`,
its failed universal
`not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`,
its reusable converse
`not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`,
the route-facing successor-cycle exact-shell package
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_any_planarBoundaryAnnulusWitnessAssignment_wheelWithInnerTriangle`,
and its failed universal
`not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`
show that even this stronger live benchmark still does not force any annulus decomposition
carrying `PlanarBoundaryAnnulusWitnessAssignment` on the same embedding.  The same successor-cycle
exact-shell witness obstruction is now also lifted to the reusable converse
`not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`,
so both the honest closed-walk and successor-cycle exact-shell obstructions are now available in
reusable witness-based form.  Any same-embedding exact one-collar/v23 example with a real Tait
coloring, nonempty purified carrier, and nonempty `V23ResidualBoundaryInitialState`, but without
annulus witness ownership on any same-embedding decomposition, already refutes a universal
derivation of that downstream decomposition-and-witness burden.  The same file now also shows
that adjoining a real local endpoint witness does not rescue that exact-shell annulus
witness-assignment lane either.  It proves the endpoint-bearing witnesses
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_any_planarBoundaryAnnulusWitnessAssignment_wheelWithInnerTriangle`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_any_planarBoundaryAnnulusWitnessAssignment_wheelWithInnerTriangle`,
their failed universals
`not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`
and
`not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`,
and the reusable converses
`not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_exists_planarBoundaryAnnulusDecomposition_and_witnessAssignment_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`.
So even on the endpoint-bearing exact-v23 one-collar honest closed-walk and successor-cycle
shells, a real Tait coloring plus `HasUnblockedInteriorEndpoint` still does not force any
same-embedding annulus decomposition carrying witness ownership.  The same file now also
packages that endpoint-bearing witness-assignment failure directly at graph-vs-fixed-embedding
level by
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_any_planarBoundaryAnnulusWitnessAssignment`
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_any_planarBoundaryAnnulusWitnessAssignment`,
so both the successor-cycle and honest-source endpoint-bearing shells now have explicit graph-
level separation theorems against same-embedding witness ownership.  The same file had already
packaged the non-endpoint version of that obstruction against the graph-level theorem-4.9
endpoint itself:
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_any_planarBoundaryAnnulusWitnessAssignment`
shows that the explicit Tait coloring still has a graph-level synthesis witness on some
embedding even while both the honest exact-v23 closed-walk shell and the successor-cycle
one-collar wheel shell fail every same-embedding witness assignment.  So the remaining
repaired-shell burden is sharper again:
before the new exact-shell synthesis theorem can apply, the route must derive witness ownership
itself, not just decomposition or face-layer data.  The same witness-assignment lane now also
retains the explicit local two-interior-edge burden at graph-vs-fixed-embedding level through
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_planarBoundaryAnnulusWitnessAssignment`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_planarBoundaryAnnulusWitnessAssignment`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_planarBoundaryAnnulusWitnessAssignment`,
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_planarBoundaryAnnulusWitnessAssignment`.
So even the annulus witness-assignment obstruction itself is now packaged with the concrete local
two-interior-edge face witness on both the non-endpoint and endpoint-bearing successor-cycle and
honest-source shells.  The same file now also proves that this
same exact-v23 one-collar wheel shell already fails to force the earliest same-embedding
boundary-free selector package even without any additional endpoint hypothesis:
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle`,
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`,
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`,
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle`,
and
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`.
So even before adjoining `HasUnblockedInteriorEndpoint`, the live exact one-collar/v23 shell
with real Tait coloring and surviving purified carrier still does not generically force even
the boundary-free selector that every later canonical-parent repair would need on the same
embedding.  The same wheel selector obstruction is now lifted to the reusable converse
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`,
so both the honest closed-walk and successor-cycle exact-shell selector obstructions are now
available in reusable witness-based form.  Any same-embedding exact one-collar/v23 example with
a real Tait coloring, nonempty purified carrier, and nonempty `V23ResidualBoundaryInitialState`,
but without a boundary-free selector, already refutes a universal derivation of that earliest
same-embedding selector burden.  The same file now also shows that adjoining a real local
endpoint witness does not rescue that exact-shell selector lane either.  It proves the
endpoint-bearing witnesses
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFreeIncidentFaceSelector_wheelWithInnerTriangle`,
their failed universals
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`
and
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`,
and the reusable converses
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`.
So even on the endpoint-bearing exact-v23 one-collar honest closed-walk and successor-cycle
shells, a real Tait coloring plus `HasUnblockedInteriorEndpoint` still does not force even the
earliest same-embedding boundary-free selector burden.  The same file now also packages this
selector failure directly at graph-vs-fixed-embedding level by
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_boundaryFreeIncidentFaceSelector`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_boundaryFreeIncidentFaceSelector`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_boundaryFreeIncidentFaceSelector`,
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_boundaryFreeIncidentFaceSelector`.
So the earliest exact-v23 selector obstruction is now graph-level source-symmetric in both its
non-endpoint and endpoint-bearing forms, instead of only appearing shell-wise before the later
bundled no-endpoint separation.  The same file then proves that this exact-v23 one-collar wheel shell already fails
to force the still-later same-embedding raw canonical-parent shared-edge-cover package under
the same no-endpoint shell:
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_wheelWithInnerTriangle`,
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`,
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_wheelWithInnerTriangle`,
and
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`.
So the raw canonical-parent cover is not the earliest obstruction on this branch either.  The
same wheel canonical-parent obstruction is now lifted to the reusable converses
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`
and
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`,
so both the honest closed-walk and successor-cycle exact-shell raw canonical-parent obstructions
are now available in reusable witness-based form.  Any same-embedding exact one-collar/v23
example with a real Tait coloring, nonempty purified carrier, and nonempty
`V23ResidualBoundaryInitialState`, but without that raw canonical-parent cover, already refutes a
universal derivation of the whole source-fixed cover burden.  The same file now also lifts this
raw canonical-parent obstruction to the endpoint-bearing exact-v23 shells:
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_wheelWithInnerTriangle`,
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`,
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_wheelWithInnerTriangle`,
and
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`.
The endpoint-bearing reusable converses
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
therefore show that even on the honest closed-walk and successor-cycle endpoint-bearing exact
one-collar/v23 shells, a real Tait coloring plus `HasUnblockedInteriorEndpoint` still does not
force the same source-fixed raw canonical-parent shared-edge-cover package.  So adding an
unblocked endpoint alone does not rescue this canonical-parent lane either.  The same file now
also packages this raw canonical-parent failure directly at graph-vs-fixed-embedding level by
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_boundaryFaceRootsCanonicalParentSharedEdgeCover`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_boundaryFaceRootsCanonicalParentSharedEdgeCover`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeCover`,
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_boundaryFaceRootsCanonicalParentSharedEdgeCover`.
So the raw canonical-parent shared-edge-cover obstruction is now graph-level source-symmetric
in both its non-endpoint and endpoint-bearing forms, instead of only appearing shell-wise before
the later parent-peel and bundled no-endpoint separations.  The
same file then also proves that this exact-v23 one-collar wheel shell already fails to force
the later same-embedding annulus-root parent-peel package under the same no-endpoint shell:
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle`,
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`,
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle`,
and
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`.
So the no-endpoint parent-peel failure is not the earliest obstruction on this branch either.
The same wheel parent-peel obstruction is now lifted to the reusable converses
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`
and
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`,
so both the honest closed-walk and successor-cycle exact-shell parent-peel obstructions are now
available in reusable witness-based form.  Any same-embedding exact one-collar/v23 example with
a real Tait coloring, nonempty purified carrier, and nonempty `V23ResidualBoundaryInitialState`,
but without annulus-root parent-peel data, already refutes a universal derivation of that whole
source-fixed parent-peel burden.  The same file now also lifts this parent-peel obstruction to
the endpoint-bearing exact-v23 shells:
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle`,
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`,
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_wheelWithInnerTriangle`,
and
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`.
The endpoint-bearing reusable converses
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
therefore show that even on the honest closed-walk and successor-cycle endpoint-bearing exact
one-collar/v23 shells, a real Tait coloring plus `HasUnblockedInteriorEndpoint` still does not
force the same source-fixed annulus-root parent-peel package.  So adding an unblocked endpoint
alone does not rescue this parent-peel lane either.  The same file now also packages this
parent-peel failure directly at graph-vs-fixed-embedding level by
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_planarBoundaryAnnulusRootParentPeelData`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_planarBoundaryAnnulusRootParentPeelData`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_planarBoundaryAnnulusRootParentPeelData`,
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_planarBoundaryAnnulusRootParentPeelData`.
So the annulus-root parent-peel obstruction is now graph-level source-symmetric in both its
non-endpoint and endpoint-bearing forms, instead of only appearing shell-wise before the later
construction-face-layer and bundled no-endpoint separations.  The same file now also lifts the
construction face-layer obstruction to the endpoint-bearing exact-v23 shells:
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle`,
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`,
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusConstructionFaceLayerData_wheelWithInnerTriangle`,
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`.
The endpoint-bearing reusable converses
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
therefore show that even on the honest closed-walk and successor-cycle endpoint-bearing exact
one-collar/v23 shells, a real Tait coloring plus `HasUnblockedInteriorEndpoint` still does not
force the downstream positive construction face-layer package.  The graph-level package
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_planarBoundaryAnnulusConstructionFaceLayerData`
now records the same diagnosis alongside explicit theorem-4.9 synthesis on some embedding.
So adding an unblocked endpoint alone does not rescue this face-layer lane either.
The same file now also proves that this
remaining burden can be reduced to a smaller honest local lemma on the stricter at-most-one
branch:
`theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge`
and
`theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge`.
So on the exact-v23 one-collar shell there is no remaining witness-assignment packaging gap once
the same embedding satisfies facewise at-most-one interior-edge cardinality.  The route file now
also exports the corresponding graph-level closures
`exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_direct`
and
`exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_direct`,
so any exact-v23 one-collar witness already carrying that honest local bound now closes directly
to full theorem-4.9 synthesis at graph level for the supplied Tait coloring.  But the same wheel
route now also records that this branch is vacuous on the present live endpoint semantics:
`not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge`,
`not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge`,
`not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_theorem49BoundaryRootNonemptyProjectedSynthesis_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge`,
and
`not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_theorem49BoundaryRootNonemptyProjectedSynthesis_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge`
show that once facewise at-most-one holds, neither `HasUnblockedInteriorEndpoint` nor the
projected nonempty theorem-4.9 endpoint can coexist with the repaired exact-v23 one-collar shell,
on either the honest closed-walk or successor-cycle presentation.  So this branch now has a fully
formalized split diagnosis: exact-v23 plus facewise at-most-one is sufficient for same-embedding
full synthesis, but incompatible with the current endpoint-bearing semantics.  This is now known
to be a genuine inhabited branch rather than a merely conditional one: the new benchmark theorems
`nonempty_diamondWithTriangleFace0_v23ResidualBoundaryInitialState`,
`diamondWithTriangle_closedWalkSource_tait_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint`,
and
`diamondWithTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint`
show that the explicit-Tait diamond benchmark already carries the repaired exact-v23 seed on the
same fixed one-collar embedding where facewise at-most-one closes to full synthesis, while both
the local endpoint witness and the projected nonempty theorem-4.9 endpoint still fail there.
The same exact-v23 repaired branch is now also shown not to force the heavier peel-data routes:
the consolidated benchmark theorems
`diamondWithTriangle_closedWalkSource_exactV23_facewiseAtMostOne_consolidatedRouteDiagnosis`
and
`diamondWithTriangle_successorCycle_exactV23_facewiseAtMostOne_consolidatedRouteDiagnosis`
show that on those same honest closed-walk and successor-cycle shells, the explicit-Tait diamond
still fails generic `InteriorDualBoundaryRootAdjDistancePeelData`, source-fixed
`PlanarBoundaryAnnulusRootAdjDistancePeelData`, and source-fixed
`PlanarBoundaryAnnulusRootParentPeelData`.  So even after adjoining the repaired exact-v23 seed
and honest facewise-at-most-one cardinality on the same embedding, these annulus-root peel lanes
remain sufficient routes only, not necessary consequences.
The same repaired exact-v23 at-most-one branch is not blocked at witness ownership either.  The
new fixed-embedding theorems
`diamondWithTriangle_closedWalkSource_tait_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint`
and
`diamondWithTriangle_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_without_hasUnblockedInteriorEndpoint_or_projectedEndpoint`
show that the exact-v23 seed, facewise at-most-one, same-embedding annulus witness assignment,
and full theorem-4.9 synthesis already coexist on the explicit-Tait diamond benchmark, on both
the honest closed-walk and successor-cycle one-collar shells, before the branch runs into the
live endpoint impossibility.  So on this repaired local branch the surviving blockers are not raw
annulus witness ownership either, but the endpoint semantics and the heavier peel-data repairs
killed just above.
The same wheel
regression file now also proves
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_without_atMostOneInteriorEdgePerFace_wheelWithInnerTriangle`,
`not_forall_atMostOneInteriorEdgePerFace_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_wheelWithInnerTriangle`,
`not_forall_atMostOneInteriorEdgePerFace_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState`,
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState_without_atMostOneInteriorEdgePerFace_wheelWithInnerTriangle`,
`not_forall_atMostOneInteriorEdgePerFace_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_wheelWithInnerTriangle`,
`not_forall_atMostOneInteriorEdgePerFace_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_v23ResidualBoundaryInitialState`,
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_atMostOneInteriorEdgePerFace`.
So this smaller honest local burden is not derivable from the live exact-v23 one-collar shell
either: the graph still has a theorem-4.9 synthesis witness on some embedding, while both the
honest closed-walk shell and the successor-cycle exact shell fail facewise at-most-one on the
fixed wheel embedding.  Any surviving repair on this branch therefore has to add new
same-embedding local geometry strictly stronger than the present exact-v23 one-collar package,
and both the honest closed-walk and successor-cycle exact-shell obstructions are now lifted to
reusable converses, so
any same-embedding exact one-collar/v23 successor-cycle example with a real Tait coloring and
nonempty `V23ResidualBoundaryInitialState`, but without facewise at-most-one interior-edge
cardinality, already refutes a universal derivation of that local-cardinality burden.  The
endpoint-bearing graph-level package
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_atMostOneInteriorEdgePerFace`
now records the same local-cardinality failure alongside explicit theorem-4.9 synthesis on some
embedding.  The same local-cardinality lane now also retains the explicit local two-interior-edge
burden at graph-vs-fixed-embedding level through
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_atMostOneInteriorEdgePerFace`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_atMostOneInteriorEdgePerFace`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_atMostOneInteriorEdgePerFace`,
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_atMostOneInteriorEdgePerFace`.
So even the local-cardinality obstruction itself is now packaged with the concrete local
two-interior-edge face witness on both the non-endpoint and endpoint-bearing successor-cycle and
honest-source shells.  This endpoint-bearing local-cardinality obstruction is therefore already
stronger than the no-endpoint parent-peel lane killed earlier on the same wheel benchmark.
The same graph-vs-fixed-embedding honest-source lift is now also available one layer earlier on
the non-endpoint wheel stack:
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_naturalResidualSameEmbeddingGeometry`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_planarBoundaryAnnulusConstructionFaceLayerData`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_any_planarBoundaryAnnulusWitnessAssignment`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_planarBoundaryAnnulusWitnessAssignment`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_atMostOneInteriorEdgePerFace`,
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_atMostOneInteriorEdgePerFace`.
So the non-endpoint exact-v23 wheel diagnostic stack is now source-symmetric at graph-vs-fixed-
embedding level from natural-residual failure, through construction-face-layer and witness-
assignment failure, up to the local-cardinality obstruction immediately below the bundled
no-endpoint collapse.
The same endpoint-bearing witness-assignment lane now also retains that explicit local
two-interior-edge burden at graph-vs-fixed-embedding level through
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_planarBoundaryAnnulusWitnessAssignment`
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_planarBoundaryAnnulusWitnessAssignment`.
So the endpoint-bearing nondegenerate witness-assignment obstruction is now source-symmetric at
graph-vs-fixed-embedding level too, not only through the coarser endpoint-bearing witness-
assignment separations without the explicit local two-edge burden.
The same endpoint-bearing local-cardinality lane now also retains that explicit local
two-interior-edge burden at graph-vs-fixed-embedding level through
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_atMostOneInteriorEdgePerFace`
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_atMostOneInteriorEdgePerFace`.
So the endpoint-bearing nondegenerate local-cardinality obstruction is now source-symmetric at
graph-vs-fixed-embedding level too, not only through the coarser endpoint-bearing local-
cardinality separations without the explicit local two-edge burden.
The same regression file now also packages that diagnosis as a single bundled no-endpoint
collapse on both exact-v23 one-collar shells:
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_currentNoEndpointRepairGeometry_wheelWithInnerTriangle`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState_without_currentNoEndpointRepairGeometry_wheelWithInnerTriangle`,
their failed universals
`not_forall_some_currentNoEndpointRepairGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`
and
`not_forall_some_currentNoEndpointRepairGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle`,
and the route-facing graph-level package
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_currentNoEndpointRepairGeometry`.
So the honest closed-walk and route-facing exact-v23 one-collar wheel shells now simultaneously
fail selector, raw canonical-parent cover, parent-peel, construction face-layer, residual
selector packages, acyclic/annulus-collar endpoints, and facewise at-most-one, while the
explicit Tait coloring still reaches theorem-4.9 synthesis on some embedding.  Any surviving
repair on this branch must therefore introduce genuinely new same-embedding geometry outside the
current no-endpoint family.  The same bundled wheel obstruction is now lifted to the reusable
converses
`not_forall_some_currentNoEndpointRepairGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`
and
`not_forall_some_currentNoEndpointRepairGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`,
so any same-embedding exact one-collar/v23 honest closed-walk or successor-cycle example with a
real Tait coloring, nonempty purified carrier, and nonempty `V23ResidualBoundaryInitialState`,
but without one of the currently known no-endpoint repairs, already refutes a universal
derivation of that whole bundled burden.  The same bundled no-endpoint wheel obstruction now also
retains its explicit local two-interior-edge face witness at graph-vs-fixed-embedding level
through
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_currentNoEndpointRepairGeometry`
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_currentNoEndpointRepairGeometry`.
So even the full bundled no-endpoint failure is now packaged together with the concrete local
reason the wheel resists canonical witness choice and facewise-at-most-one collapse, not only as
a coarse disjunction of missing repair layers.
The same regression file now also shows that adjoining a real local endpoint witness does not
rescue that bundled no-endpoint lane either.  It proves the endpoint-bearing witnesses
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_currentNoEndpointRepairGeometry_wheelWithInnerTriangle`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_currentNoEndpointRepairGeometry_wheelWithInnerTriangle`,
their failed universals
`not_forall_some_currentNoEndpointRepairGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`
and
`not_forall_some_currentNoEndpointRepairGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`,
and the reusable converses
`not_forall_some_currentNoEndpointRepairGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_some_currentNoEndpointRepairGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`.
So even on the endpoint-bearing exact-v23 one-collar honest closed-walk and successor-cycle
shells, a real Tait coloring plus `HasUnblockedInteriorEndpoint` still fails every currently
bundled no-endpoint repair.  Adding an unblocked endpoint alone therefore does not escape the
wheel obstruction on this lane either.  The new graph-level package
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_currentNoEndpointRepairGeometry`
now records that same endpoint-bearing bundled failure alongside explicit theorem-4.9 synthesis
on some embedding.  So this branch is now calibrated at graph-vs-fixed-embedding level too:
even after adjoining a real unblocked endpoint on the live exact-v23 one-collar wheel shell, the
graph-level positive witness still sits strictly upstream of every currently bundled no-endpoint
same-embedding repair.  The honest-source side is now packaged at the same graph-vs-fixed-
embedding level too by
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_currentNoEndpointRepairGeometry`.
So both endpoint-bearing exact-v23 one-collar source presentations now have explicit graph-level
separation theorems against the full bundled no-endpoint repair family.  The same endpoint-
bearing bundled obstruction now also retains the explicit local two-interior-edge face witness at
that graph-vs-fixed-embedding level through
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_currentNoEndpointRepairGeometry`
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_currentNoEndpointRepairGeometry`.
So the full endpoint-bearing no-endpoint wheel obstruction is now nondegenerate and source-
symmetric too, not only the earlier componentwise selector / face-layer / witness-assignment /
local-cardinality layers below it.
The same replacement-positive lane is now graph-level source-symmetric even before adjoining an
endpoint: the regression file proves
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_any_replacementPositiveProjectedGeometryOn`
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_without_any_replacementPositiveProjectedGeometryOn`.
So the exact-v23 one-collar wheel already separates graph-level theorem-4.9 synthesis from every
current direct or route-facing replacement-positive package on both the successor-cycle and honest
closed-walk source presentations, not only from the coarser bundled
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_replacementPositiveProjectedGeometry_or_previousBoundaryWitness`
theorem or the later endpoint-bearing replacements.
The same non-endpoint replacement-positive lane now also keeps the explicit local two-interior-edge
burden at graph level through
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_replacementPositiveProjectedGeometryOn`
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_replacementPositiveProjectedGeometryOn`.
So this nondegenerate replacement-positive wheel obstruction is now source-symmetric at graph
level too, not only shell-local on the successor-cycle benchmark or later via the
endpoint-bearing replacement-positive package.
The same later construction-face-layer branch now keeps that explicit local two-interior-edge
burden at graph level too through
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData`
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData`.
So the nondegenerate face-layer wheel obstruction is now source-symmetric at graph-vs-fixed-
embedding level as well, not only shell-local on the successor-cycle benchmark.
The same endpoint-bearing face-layer lane now also keeps that explicit local two-interior-edge
burden at graph level through
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData`
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_and_twoDistinctInteriorEdgesOnFaceBoundary_without_planarBoundaryAnnulusConstructionFaceLayerData`.
So the endpoint-bearing nondegenerate face-layer wheel obstruction is now source-symmetric at
graph-vs-fixed-embedding level too, not only through the coarser endpoint-bearing face-layer
separations without the explicit local two-edge burden.
The same graph-vs-fixed-embedding honest-source lift is now also available for the earlier
endpoint-bearing wheel obstruction layers
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_currentSufficientSameEmbeddingGeometry`,
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_planarBoundaryAnnulusConstructionFaceLayerData`,
and
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_closedWalkSource_hasUnblockedInteriorEndpoint_without_atMostOneInteriorEdgePerFace`.
So the full endpoint-bearing wheel diagnostic stack is now source-symmetric at graph level from
replacement-positive, through current-sufficient, construction-face-layer, and local-cardinality
failure, all the way up to the bundled no-endpoint repair family.
The same regression file now also shows that simply adjoining the honest local endpoint witness
does not rescue the replacement-positive lane.  It proves
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_any_replacementPositiveProjectedGeometryOn_wheelWithInnerTriangle`,
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_twoDistinctInteriorEdgesOnFaceBoundary_without_any_replacementPositiveProjectedGeometryOn_wheelWithInnerTriangle`,
its failed universals
`not_forall_any_replacementPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`
and
`not_forall_any_replacementPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`,
and the graph-level package
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn`.
So even the endpoint-bearing exact-v23 one-collar wheel shell still fails every current direct
or route-facing replacement-positive package on both the honest closed-walk and successor-cycle
boundary-order shells, and on the successor-cycle shell this coexists with a concrete
two-interior-edge face boundary, although the explicit Tait coloring reaches theorem-4.9
synthesis on some embedding.  Adding `HasUnblockedInteriorEndpoint` alone therefore does not
escape the wheel obstruction either; any surviving endpoint-bearing positive repair must add
genuinely new same-embedding geometry beyond the present replacement-positive family.  The same
wheel obstruction is now lifted to the reusable converses
`not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_any_replacementPositiveProjectedGeometryOn_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`,
so any same-embedding exact one-collar/v23 example with a real Tait coloring,
`HasUnblockedInteriorEndpoint`, and nonempty `V23ResidualBoundaryInitialState`, but without one
of the current direct or route-facing replacement-positive endpoints, already refutes a
universal derivation of that whole burden.
The larger endpoint-bearing `currentSufficientSameEmbeddingGeometry` target on this wheel shell
now collapses on both the honest closed-walk and successor-cycle exact-v23 shells.  The theorems
`currentSufficientSameEmbeddingGeometry_wheelWithInnerTriangle_only_if_attachedBoundaryRootedFacePeelCertificate`,
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_reducing_currentSufficientSameEmbeddingGeometry_to_attachedBoundaryRootedFacePeelCertificate_wheelWithInnerTriangle`,
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_reducing_currentSufficientSameEmbeddingGeometry_to_attachedBoundaryRootedFacePeelCertificate_wheelWithInnerTriangle`
show that on the live endpoint-bearing exact-v23 wheel shells, the height-ordered,
collar-layer, well-founded, and annulus-collar branches were already ruled out, so any future
proof on either shell reduces to the raw attached certificate on the same embedding.  The wheel
certificate obstruction
`not_nonempty_attachedBoundaryRootedFacePeelCertificate_wheelWithInnerTriangle`
then kills that last branch as well, and the bundled witnesses
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_currentSufficientSameEmbeddingGeometry_wheelWithInnerTriangle`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_currentSufficientSameEmbeddingGeometry_wheelWithInnerTriangle`,
together with the failed universals
`not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`
and
`not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_wheelWithInnerTriangle`,
show that even the endpoint-bearing exact-v23 honest closed-walk and successor-cycle shells
still do not force any of the currently sufficient same-embedding geometry endpoints on the
fixed wheel embedding.  The new generic converses
`not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
and
`not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState`
now lift that same exact-shell current-sufficient failure to reusable witness-based refutations:
any same-embedding exact one-collar/v23 honest closed-walk or successor-cycle example with a
Tait coloring, `HasUnblockedInteriorEndpoint`, and nonempty
`V23ResidualBoundaryInitialState`, but without one of the current sufficient geometry
endpoints, already kills any universal derivation of that whole burden.  The
live-carrier predecessor shell now has the same reusable converse:
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_and_v23ResidualBoundaryInitialState`.
So any same-embedding exact one-collar/v23 successor-cycle example with a Tait coloring,
nonempty purified carrier, and nonempty `V23ResidualBoundaryInitialState`, but without one of
the current natural residual same-embedding endpoints, already refutes any universal derivation
of that whole live-carrier burden as well.  The
graph-level package
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_hasUnblockedInteriorEndpoint_without_currentSufficientSameEmbeddingGeometry`
now records the same diagnosis alongside explicit theorem-4.9 synthesis on some embedding for the
same Tait coloring.  So any surviving endpoint-bearing theorem-4.9 repair must add genuinely new
same-embedding geometry outside the present current-sufficient family, not merely revive one of
its existing branches.
The selector-deficit face-contact premise is now also isolated as the smallest genuinely local
repair.  `Theorem49BoundaryFreeSelectorConstruction.lean` proves
`selectorDeficitSelectedBoundary_of_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary`,
and `Theorem49ResidualBoundaryRoute.lean` uses it in
`theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_resultingDecompositionWitnessAssignment`.
So whenever the stronger older hypothesis already shows that every non-peeled construction face
meets selected-boundary support on the same parent-peel construction, the repaired
selector-deficit premise is no longer independent.  `Theorem49ResidualBoundaryRoute.lean` now
also proves
`nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionFaceLayerData`,
`theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData_and_inducedDecompositionWitnessAssignment`,
`theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData_and_resultingDecompositionWitnessAssignment`,
`nonempty_planarBoundaryAnnulusDecomposition_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData`
and
`theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_inducedDecompositionWitnessAssignment`,
`theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData_and_resultingDecompositionWitnessAssignment`.
So once the route reaches `PlanarBoundaryAnnulusConstructionFaceLayerData`, annulus
decomposition is automatic and the full theorem-4.9 endpoint reduces exactly to witness
ownership on the exact annulus decomposition canonically induced by that shell.  The stronger selected-boundary
`PlanarBoundaryAnnulusConstructionBoundarySupportFaceData` shell is now only an upstream way to
reach that face-layer package, not part of the downstream closure theorem itself.  The same file
now also proves the graph-level route wrappers
`exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_planarBoundaryAnnulusConstructionFaceLayerData_and_resultingDecompositionWitnessAssignment_direct`,
the stronger selected-boundary-support analogue, and the matching successor-cycle pair.  So once
the honest-source or successor-cycle route reaches either same-embedding construction shell and
the resulting decomposition carries witness ownership, full `Theorem49BoundaryRootSynthesis`
already follows directly at graph level; no further repackaging step remains below that shell.
`Theorem49PositiveGeometricSourceReplacement.lean` now also proves
`theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData`,
`theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstructionFaceLayerData`,
`theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryAnnulusConstructionFaceLayerData`,
`theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData`,
`theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData`,
and
`theorem49BoundaryRawQuotientErrorPackage_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData`.
So once either construction shell exists on the same embedding, full
`Theorem49BoundaryRootSynthesis` is already automatic directly in the positive replacement
file itself, and a surviving purified carrier is only needed to upgrade further to the current
replacement-positive projected endpoint and its raw quotient/error package.  The remaining
burden therefore lies strictly earlier, in deriving that carrier or stronger source-side
geometry, not in any further downstream replacement lowering.
`Theorem49PositiveGeometricSourceReplacementRoute.lean` now also proves the graph-package
methods
`Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry.boundaryRootSynthesis`,
`Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry.exists_boundaryRootSynthesis`,
and the matching successor-cycle pair.  So once those named construction-face-layer route
packages themselves carry witness ownership on the same derived annulus decomposition, full
`Theorem49BoundaryRootSynthesis` follows immediately; there is no remaining repackaging gap
between those graph-level route objects and the theorem-4.9 endpoint.
`Theorem49PositiveGeometricSourceReplacementRoute.lean` now also packages the stronger
selected-boundary-contact shell itself as the fixed-embedding predicates
`Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn` and
`Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometryOn`,
together with the graph-level structures
`Theorem49ClosedWalkAnnulusConstructionBoundarySupportPositiveProjectedGeometry` and
`Theorem49SuccessorCycleAnnulusConstructionBoundarySupportPositiveProjectedGeometry`.  Those
graph packages already expose `boundaryRootSynthesis` and `exists_boundaryRootSynthesis` on
the induced annulus decomposition, so callers no longer need to first repackage this shell as
construction-face-layer route data just to state the direct theorem-4.9 closure.  The same
file still packages the derived face-layer closure as the fixed-embedding predicates
`Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometryOn` and
`Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometryOn`, together with
the graph-level structures
`Theorem49ClosedWalkAnnulusConstructionFaceLayerPositiveProjectedGeometry` and
`Theorem49SuccessorCycleAnnulusConstructionFaceLayerPositiveProjectedGeometry`.  The stronger
selected-boundary-contact shell still lowers directly into those derived face-layer route
surfaces via
`PlanarBoundaryAnnulusConstructionBoundarySupportFaceData.toPlanarBoundaryAnnulusConstructionFaceLayerData`.
So once the live honest-source or successor-cycle route reaches same-embedding
`PlanarBoundaryAnnulusConstructionFaceLayerData` and still carries
`HasUnblockedInteriorEndpoint`, the current projected theorem-4.9 endpoint, the raw
quotient/error package, and the replacement-positive height/collar packages already follow
directly, without any further collar-geometry or well-founded-witness detour.
That diagnosis is now repaired again.  `Theorem49BoundaryFreeSelectorConstruction.lean` proves
`parentWitnessOrientation_of_boundaryData_and_interiorDualBoundaryRootParentPeelData`,
`parentWitnessOrientation_of_planarBoundaryAnnulusRootParentPeelData`, and
`not_exists_planarBoundaryAnnulusConstructionBoundarySupportFaceData_with_planarBoundaryAnnulusRootParentPeelConstruction`.
So the exact selector-driven parent-peel construction is already
`PlanarBoundaryAnnulusConstruction.ParentWitnessOrientation` on the same embedding, while any
same-construction selected-boundary-support shell still forbids parent orientation.  The same
construction file now isolates the resulting contradiction at the actual shell that creates it:
`false_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary`
and
`false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary`.
The same construction file now also packages this as raw boundary-order graph-level
nonexistence theorems:
`not_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary`
and
`not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary`.
It also now gives the fixed-embedding local nonexistence forms
`not_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace`
and
`not_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc`,
which are the direct reusable statements downstream route arguments should consume.
So the repaired selector-deficit plus positive-current-boundary package is already globally
impossible before any exact one-collar or exact-v23 residual hypotheses are added.
`Theorem49ResidualBoundaryRoute.lean` then re-exports this at the repaired exact one-collar shell
itself with
`false_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary`
and
`false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary`.
So the old positive `currentOuterBoundary` side conditions are not merely another local burden to
derive on the same parent-peel construction: they are incompatible with that construction.  The
earlier exact-shell face-layer, decomposition, and synthesis theorems with those hypotheses
remain valid but vacuous.  The same route file now also states that the stronger older
non-peeled-face selected-boundary-contact repair collapses for the same reason:
`false_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary`
and
`false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary`.
So the stronger `nonPeelSelectedBoundary` branch is not merely reducible to the selector-deficit
branch inside later synthesis theorems; it is already directly inconsistent with the same old
positive current-boundary side conditions.  `Theorem49ResidualBoundaryRoute.lean` now also packages this as direct
graph-level nonexistence theorems:
`not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary`
and
`not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary`.
So this repaired selector-deficit plus positive-current-boundary shell is not merely unforced by
the live route: even the stricter exact-shell witness form is globally impossible, as an
immediate corollary of the boundary-order contradiction above.  The matching stronger
non-peeled-face graph-level nonexistence theorems are now present too:
`not_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary`
and
`not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary`.
So even that stronger repair branch is globally impossible on the exact shell.  `Theorem49ResidualBoundaryObstruction.lean` now upgrades that from a
local contradiction to direct exact-shell failed universals:
`not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
and
`not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`,
with the matching forcing-edge abstract converse failures.  It now also exposes the exact-shell
counterexamples themselves as
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_sharedInteriorPair`.
So even the full repaired selector-deficit plus positive-current-boundary package is not forced
by the live exact shell on the shared-interior-pair benchmark.  The same obstruction file now
upgrades the stronger older non-peeled-face branch in the same way:
`not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
and
`not_forall_exists_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`,
with the matching exact-shell counterexamples
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary_sharedInteriorPair`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary_and_currentOuterBoundary_sharedInteriorPair`.
So even that stronger older repair is not forced by the live exact shell on the same benchmark.
The live route must therefore
avoid that positive-frontier shell entirely and continue through the already parent-oriented
construction / well-founded-parent lane.
`Theorem49ResidualBoundaryRoute.lean` now also proves the direct exact-shell endpoint theorems
`theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData`
and
`theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData`.
So once the exact one-collar shell carries same-split annulus-root parent peel data at all, the
full Theorem~4.9 synthesis endpoint is already immediate on that embedding; the selector-deficit
and positive-current-boundary detour is not just unnecessary but inconsistent on that same
construction.  So the remaining issue is not any further downstream lowering below
`PlanarBoundaryAnnulusRootParentPeelData`, but whether the current exact shell forces that
package at all.  The same file now also proves the even earlier exact-shell theorems
`theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover`
and
`theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover`,
together with the matching graph-level direct existence forms.  So once the exact one-collar shell
already carries the raw source-fixed canonical-parent shared-edge cover on the extracted
boundary-face roots, full `Theorem49BoundaryRootSynthesis` is already immediate on that
embedding, with no `HasUnblockedInteriorEndpoint` and no separate parent-peel repackaging step.
The live exact-shell burden is therefore sharper again: force that concrete source-fixed
shared-edge cover itself, or prove that the repaired shell cannot support it.  The same file now
also proves the exact-shell selector-side lowerings
`theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector`
and
`theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_boundaryFreeSelector`,
together with the matching graph-level existential forms.  So once that same exact shell carries
the raw source-fixed canonical-parent shared-edge cover together with
`HasUnblockedInteriorEndpoint`, it already lands on the named
`Theorem49HeightOrderedPositiveProjectedGeometryOn` surface before any residual-boundary
repackaging.  The same file now
also proves the sharper exact-shell rooted shared-edge face-membership theorems
`theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover`
and
`theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover`,
together with the matching graph-level direct existence forms.  So once the repaired exact shell
already carries the concrete source-fixed rooted shared-edge face-membership cover package on the
extracted boundary-face roots, full `Theorem49BoundaryRootSynthesis` is immediate on that same
embedding, with no further descent either through canonical-parent cover packaging or through the
generic IDBRAD shell.  The live exact-shell burden can therefore be stated at that sharper
source-facing rooted-cover layer itself.  The same file now also proves the exact-shell
height-ordered lowerings
`theorem49HeightOrderedPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint`
and
`theorem49HeightOrderedPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint`,
together with the matching graph-level existential forms.  So once that same exact shell carries
the concrete rooted shared-edge face-membership cover together with
`HasUnblockedInteriorEndpoint`, it already lands on the named
`Theorem49HeightOrderedPositiveProjectedGeometryOn` surface, not just on the intermediate
annulus-root adjacency-distance package.  The same file now also proves the direct exact-shell
finite-collar lowerings
`theorem49CollarLayerPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint`
and
`theorem49CollarLayerPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint`,
together with the matching graph-level existential forms.  So that same exact shell now also
lands directly on the named `Theorem49CollarLayerPositiveProjectedGeometryOn` surface itself,
not only after passing through the height-ordered route surface or the later residual-boundary
positive interface.  The same file now
also proves the exact-shell theorems
`theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData`
and
`theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData`.
So on the exact one-collar v23/v23.5 shell, even the annulus-root parent-peel package is no
longer the minimal positive burden: it already suffices to derive generic
`InteriorDualBoundaryRootAdjDistancePeelData` on the same embedding, or any equivalent
cycle-breaking parent witness strong enough to construct it.  `Theorem49ResidualBoundaryRoute.lean`
now also proves the exact-shell route-surface lowerings
`theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint`,
`theorem49SuccessorCycleAnnulusRootParentPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint`,
`theorem49ClosedWalkAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint`,
and
`theorem49SuccessorCycleAnnulusRootAdjDistancePositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint`.
So the live exact shell no longer merely has ad hoc endpoint corollaries: once it carries the
parent-peel or generic adj-distance package together with `HasUnblockedInteriorEndpoint`, it
already lands on the named root-parent or root-distance positive route surfaces used elsewhere in
the replacement pipeline.  The same file now also packages the corresponding graph-level
existential forms through
`nonempty_theorem49ClosedWalkAnnulusRootParentPositiveProjectedGeometry_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint`,
its successor-cycle analogue, and the matching root-distance pair.  So downstream graph-level
route consumers can now use the live exact shell directly, without rebuilding those positive
packages by hand.  `Theorem49PositiveGeometricSourceReplacementRoute.lean` now also gives those
four graph-level positive route packages their own `boundaryRootSynthesis` and
`exists_boundaryRootSynthesis` methods, so once the exact shell has lowered into the named
root-parent or root-distance surfaces, no further manual descent through collar-layer packages is
needed to recover full Theorem~4.9 synthesis.  `Theorem49PositiveGeometricSourceReplacementJointObstruction.lean`
now proves that these same four named root-parent/root-distance positive route surfaces
(closed-walk and successor-cycle variants alike) jointly impose two local burdens on the same
embedding: some face boundary must contain two distinct interior edges, and forcing interior-edge
witnesses are impossible there.  So the constructive parent-oriented positive lane now exposes an
honest combined structural profile rather than only endpoint closure.  More sharply, those same
four packages now already prove `EveryInteriorEdgeHasBoundaryFreeIncidentFace` and supply
concrete `BoundaryFreeIncidentFaceSelector` data on the same embedding, so the local
boundary-free selector shell is no longer a downstream burden below those positive route
packages.  The same file now closes
one step lower still: it
proves the direct exact-shell
graph-level endpoint and raw quotient/error wrappers
`exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_direct`,
its successor-cycle analogue, the matching generic adj-distance pair, and the four corresponding
`exists_theorem49BoundaryRawQuotientErrorPackage...` theorems.  So once the exact shell already
carries parent-peel or generic adj-distance data together with `HasUnblockedInteriorEndpoint`, the
route no longer needs even an explicit graph-level positive-surface unpacking step before reaching
the current theorem-4.9 projected endpoint or raw quotient/error package.  The same file now also
proves the direct graph-level full-synthesis closures
`exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_planarBoundaryAnnulusRootParentPeelData_direct`,
its successor-cycle analogue, and the matching generic adj-distance pair.  So once the live exact
shell already carries same-embedding parent-peel data or generic adj-distance data at all, the
route now reaches full `Theorem49BoundaryRootSynthesis` directly; even the projected-endpoint or
positive-surface packaging steps are no longer downstream burdens below that shell.
`Theorem49ResidualBoundaryPeeling.lean` now also proves
`theorem49BoundaryRootSynthesis_of_residualBoundarySelectorData`,
`theorem49BoundaryRootSynthesis_of_residualBoundaryLayerFacePeelWitnessData`, and
`theorem49BoundaryRootSynthesis_of_residualBoundaryPositiveProjectedGeometryOn`, while
`Theorem49ResidualBoundaryRoute.lean` proves
`theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundarySelectorData`
and
`theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData`,
the successor-cycle analogue
`theorem49BoundaryRootSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData`,
and the graph-level direct closures
`exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_direct`
and
`exists_theorem49BoundaryRootSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_direct`.
So once the route reaches residual/current-boundary selector data itself, the full
Theorem~4.9 synthesis endpoint is already immediate on that embedding; the lower residual
witness package and `HasUnblockedInteriorEndpoint` are no longer downstream burdens beyond that
surface, and even the route-facing successor-cycle shell now exports that same residual-layer
synthesis package directly at graph level.  `Theorem49ResidualBoundaryRoute.lean` also proves the
route-facing projected-endpoint lift
`theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint`
and its graph-level direct closure
`exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct`.
`Theorem49ResidualBoundaryPeeling.lean` now also proves
`nonempty_residualBoundarySelectorData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData`
and
`nonempty_residualBoundarySelectorData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_interiorDualBoundaryRootAdjDistancePeelData`.
So the residual selector surface is no longer the first unresolved layer above the live
parent-oriented shell: generic `InteriorDualBoundaryRootAdjDistancePeelData` already lowers to
that surface on the same embedding.  The live constructive burden therefore sharpens again to
deriving that adjacency-distance package, or any equivalent cycle-breaking parent witness strong
enough to build residual/current-boundary selector data.  `Theorem49ResidualBoundaryPeeling.lean`
now also proves
`theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint`
and
`theorem49CurrentBoundaryRemainders_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData_and_hasUnblockedInteriorEndpoint`,
while `Theorem49ResidualBoundaryRoute.lean` adds the exact one-collar closed-walk and
successor-cycle wrappers.  So once the same embedding carries generic
`InteriorDualBoundaryRootAdjDistancePeelData` together with `HasUnblockedInteriorEndpoint`, the
route already recovers both residual/current-boundary positive projected geometry and a concrete
layer-face current-boundary remainder witness there.  These lower residual surfaces are therefore
not any additional constructive burden below the adjacency-distance package; they are already
downstream consequences of it.  The same route file now also exposes those residual/current-
boundary consequences one layer higher on the exact same-split parent-peel shell itself, together
with matching graph-level existential closures.  So once the live exact shell reaches
`PlanarBoundaryAnnulusRootParentPeelData` together with `HasUnblockedInteriorEndpoint`, the
residual interface is already present there as well; downstream users no longer need to unpack the
intermediate annulus-parent positive package or rebuild existential residual witnesses by hand.
More sharply, `Theorem49ForcingInteriorEdgeObstruction.lean` now
also exposes explicit `BoundaryFreeIncidentFaceSelector` constructors from both generic
`InteriorDualBoundaryRootAdjDistancePeelData` and `PlanarBoundaryAnnulusRootAdjDistancePeelData`,
while `Theorem49ResidualBoundaryRoute.lean` adds the exact one-collar closed-walk and
successor-cycle wrappers for both same-split annulus-root parent-peel data and generic
adjacency-distance data.  So once the live exact shell reaches either of those parent-oriented
packages at all, the local boundary-free selector shell is already present on the same embedding;
that selector burden is no longer downstream of the parent/adjacency-distance stage.
`Theorem49ResidualBoundaryObstruction.lean` now calibrates that same burden directly on the live
exact one-collar/v23 shared-interior-pair shell.  It proves
`sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_without_interiorDualBoundaryRootAdjDistancePeelData`
and
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_interiorDualBoundaryRootAdjDistancePeelData_sharedInteriorPair`,
together with the closed-walk and successor-cycle failed-universal forms.  So the current live
adjacency-distance burden is not merely unproved on that benchmark: even exact one-collar
current-boundary data, a real Tait coloring, `HasUnblockedInteriorEndpoint`, and the exact
v23 residual initial state still do not force any same-embedding generic
`InteriorDualBoundaryRootAdjDistancePeelData` there.
The same repaired exact shell now also fails one layer later at the actual two-sided annulus-root
route package itself.  `Theorem49ResidualBoundaryObstruction.lean` proves
`not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_sharedInteriorPair`,
`sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootAdjDistancePeelData`,
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootAdjDistancePeelData_sharedInteriorPair`,
and the matching closed-walk / successor-cycle failed-universal theorems.  The same obstruction is
now lifted to reusable forcing-edge converse failures too:
`not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness`
and
`not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness`.
So the current live shell does not merely fail to force generic interior-dual peel data: it already
fails to force the source-preserving two-sided annulus-root adjacency-distance route package on the
same embedding.
The same file now also proves
`not_nonempty_planarBoundaryAnnulusRootParentPeelData_sharedInteriorPair`,
`sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData`,
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_planarBoundaryAnnulusRootParentPeelData_sharedInteriorPair`,
and the matching closed-walk / successor-cycle failed-universal theorems.  So the same repaired
exact one-collar/v23 shell does not merely fail at the stronger generic adjacency-distance
package: it already fails to force the actual same-embedding
`PlanarBoundaryAnnulusRootParentPeelData` route target itself.  The live diagnosis is therefore
sharper than “derive parent-peel from the residual shell”: that implication is false on the
current shell, so the route must either strengthen the upstream same-embedding hypotheses or turn
the residual shell into an impossibility theorem instead of continuing to lower downstream.  The
same obstruction is now lifted from the benchmark instance to reusable route-level failed-universal
theorems too:
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness`
and
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_and_forcingInteriorEdgeWitness`.
So whenever one exhibits any same-embedding exact-shell witness together with a forcing interior
edge, the parent-peel converse is formally refuted on that shell, not only on the single
shared-interior-pair example.
`Theorem49InteriorVerticesEndpointObstruction.lean` now also exposes the opposite concrete
calibration: `nonempty_interiorDualBoundaryRootAdjDistancePeelData_peeledEndpointTouch` and
`admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph`
show that generic boundary-root adjacency-distance data is itself realizable on a concrete
benchmark, but only off the live source-preserving route.  The endpoint-touch graph is acyclic, so
it cannot satisfy the honest closed-walk annulus source at all.  Thus the shared-interior-pair
exact-shell failure isolates a source-compatible obstruction on the live route, not any absolute
impossibility of `InteriorDualBoundaryRootAdjDistancePeelData` itself.
`Theorem49ForcingInteriorEdgeObstructionRegression.lean` now strengthens that diagnosis on an
honest source-compatible benchmark too.  The chained-diamonds source already inhabits the stronger
local package `exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph`,
which is enough elsewhere in the development to derive canonical witness choice and weak collar
geometry.  But the new theorems
`not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness`
and
`not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph`
show that even this stronger honest closed-walk source package still does not force generic
boundary-root adjacency-distance data on the same embedding.  So the adj-distance obstruction is
not peculiar to the repaired exact one-collar/v23 shell; it already appears higher up on a
source-compatible local source surface.  The same file now also proves
`not_nonempty_planarBoundaryAnnulusRootParentPeelData_chainedDiamondsWithTriangle_via_forcingInteriorEdgeWitness`
and
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph`,
so even that stronger honest-source package still does not force the current parent-oriented
annulus-root target on the same embedding.  This sharpens the live burden again: the route now
needs genuinely stronger source-side structure than the chained-diamonds at-most-one package, not
just more downstream lowering from it.  `Theorem49PlanarBoundaryAnnulusHonestGeometryRegression.lean`
now also proves
`exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_chainedDiamondsWithTriangleGraph_with_empty_carrier_and_without_taitEdgeColoring`,
so this same honest source-compatible benchmark already reaches exact one-collar current-boundary
data and split-annulus witness assignment on the same embedding.  Even there the purified carrier
stays empty and no Tait coloring exists.  The stronger theorem
`exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_for_any_taitEdgeColoring_chainedDiamondsWithTriangleGraph_without_any_taitEdgeColoring`
now shows that any hypothetical Tait coloring would already close to full `Theorem49BoundaryRootSynthesis`
on that same embedding.  Thus on the chained-diamonds at-most-one branch the live blocker for the
theorem-4.9 endpoint is Tait colorability itself, not more exact-shell or witness-assignment
packaging.  `Theorem49PlanarBoundaryAnnulusHonestGeometryRegression.lean`
then gives the same diagnosis on the closer diamond-with-triangle collar/certificate surface:
`closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle`
shows that even honest source data together with a weak one-collar annulus geometry and an attached
rooted face-peel certificate still does not force `PlanarBoundaryAnnulusRootParentPeelData` on a
genuine cyclic source model.  So the direct certificate lane is already strictly earlier than the
live parent-peel burden too.  The same file now also proves
`exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangleGraph`,
`exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph`,
`exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph`,
and the converse failures
`not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph`,
`not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph`,
and
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph`.
So this is no longer merely a benchmark-local fact about the weak certificate shell in isolation:
even after that same honest collar/certificate shell already carries an explicit Tait coloring and
the full `Theorem49BoundaryRootSynthesis` endpoint on one embedding, none of the current generic,
source-preserving, or live parent-peel adj-distance burdens are necessary consequences there.  The
direct certificate lane therefore remains strictly earlier than all three of those parent-oriented
routes even post-synthesis.  The same file now also proves
`diamondWithTriangle_explicitTait_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_theorem49BoundaryRootSynthesis_blocks_nonemptyProjectedSynthesis`,
`exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph`,
and
`not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph`.
So the same weak collar/certificate shell is already too weak not only for the parent-oriented
adj-distance targets, but even for the projected nonempty theorem-4.9 endpoint itself: after
full synthesis closes on that same embedding, the selected-boundary-purified carrier is still
empty.  Thus the direct certificate lane is strictly earlier than the projected endpoint route
too, not merely than the parent-peel derivations lying above it.  The same file now also proves
`diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_consolidatedRouteDiagnosis`,
which packages the whole same-embedding calibration on that genuine cyclic source model: the full
current positive geometry stack and explicit-Tait theorem-4.9 synthesis coexist with a nonempty
raw interior-edge endpoint carrier, an empty purified carrier, failure of the projected nonempty
endpoint, failure of generic `InteriorDualBoundaryRootAdjDistancePeelData`, and failure of the
live parent-peel package.  The more specialized theorems
`diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_interiorDualBoundaryRootAdjDistancePeelData`
and
`diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_planarBoundaryAnnulusRootAdjDistancePeelData`,
and
`diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_planarBoundaryAnnulusRootParentPeelData`
remain available as focused projections of that same diagnosis.  The same file now also proves
`exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph`
and
`not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph`,
so this obstruction is no longer merely benchmark-local: the full honest-source/current-geometry
stack plus theorem-4.9 synthesis already refutes the generic converse to
`Theorem49BoundaryRootNonemptyProjectedSynthesis` on that graph.  The same file now also proves
`exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangleGraph`,
`exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph`,
`exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph`,
and the converse failures
`not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph`,
`not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph`
and
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph`.
So even the full current same-embedding positive geometry stack plus full theorem-4.9 synthesis is
still not enough to force generic interior-dual adj-distance data, source-preserving
annulus-root adj-distance data, or the live parent-peel package on that genuine cyclic source
benchmark.  The same file now also proves
`diamondWithTriangle_explicitTait_synthesis_without_interiorDualBoundaryRootAdjDistancePeelData`,
`diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData`,
and
`diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootParentPeelData`,
so even the bare theorem-4.9 synthesis endpoint under the explicit Tait coloring coexists with
failure of the generic interior-dual adj-distance package, the source-preserving annulus-root
adj-distance package, and the live parent-peel package on that same embedding.  Thus none of
those parent-oriented burdens is necessary even for a genuine cyclic positive synthesis model;
they are only sufficient routes among others.  This is now lifted to a reusable converse-failure theorem too:
`Theorem49ForcingInteriorEdgeObstruction.lean` proves
`not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness`,
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness`,
and `Theorem49ForcingInteriorEdgeObstructionRegression.lean` instantiates them on the diamond
model via
`exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness_diamondWithTriangleGraph`,
`not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangle_via_forcingInteriorEdgeWitness`,
and
`not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangle_via_forcingInteriorEdgeWitness`.
So any synthesis model carrying a forcing interior edge now formally refutes the universal converse
from full theorem-4.9 synthesis back to either same-embedding annulus-root adjacency-distance data
or same-embedding parent-peel data.
`Theorem49ForcingInteriorEdgeObstructionRegression.lean` now also records the complementary
graph-vs-embedding separation on the wheel benchmark.
`exists_theorem49BoundaryRootSynthesis_wheelWithInnerTriangleGraph_via_degenerateAttachedCertificate`
shows that the wheel graph still admits the full theorem-4.9 synthesis endpoint for the explicit
Tait coloring on some embedding via the degenerate all-boundary certificate route, while
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_IDBRAD_obstruction`
packages that graph-level positive fact together with the honest source-preserving wheel embedding's
Tait coloring, explicit unblocked interior endpoint, and failure of generic same-embedding
`InteriorDualBoundaryRootAdjDistancePeelData`.  So the current wheel obstructions are genuinely
source-preserving same-embedding route failures, not graph-level impossibility of theorem-4.9
synthesis for that colored graph.  The new theorem
`wheelWithInnerTriangleGraph_explicitTait_degenerateSynthesis_blocks_nonemptyProjectedSynthesis`
sharpens the positive side of that comparison: the current graph-level witness is exactly the
degenerate all-boundary embedding, so it reaches full synthesis only on an embedding whose
selected-boundary-purified interior-edge endpoint carrier is empty and therefore cannot witness
`Theorem49BoundaryRootNonemptyProjectedSynthesis`.  Thus the currently known wheel graph-level
positive theorem still sits entirely off the projected nonempty lane.  The new theorem
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_requires_embedding_change`
sharpens that diagnosis one step further: the currently known graph-level witness is provably not
the honest source-preserving wheel embedding at all, because the degenerate witness has empty
selected-boundary-purified carrier while the honest wheel embedding has a surviving purified
carrier.  So the present wheel positivity result necessarily changes embeddings before it can fire.
The stronger theorem
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_selector_or_acyclicEndpoint_or_IDBRAD`
shows that this same separation already covers every currently sufficient same-embedding
selector/acyclic endpoint on the honest wheel embedding too: with the same explicit Tait coloring,
honest source, nonempty purified carrier, and explicit unblocked interior endpoint, the fixed wheel
embedding still has no boundary-free selector, no well-founded/height-ordered/collar-layer witness
surface, no weak annulus-collar geometry, and no generic same-embedding
`InteriorDualBoundaryRootAdjDistancePeelData`.  The new theorem
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_sameEmbedding_projectedSourceRoutes`
pushes that same wheel diagnosis all the way to the currently formalized projected endpoint routes:
the graph still admits full theorem-4.9 synthesis on some embedding, but on the honest
source-preserving wheel embedding the same explicit Tait coloring still cannot instantiate either
the IDBRAD-based projected endpoint route or the source-fixed canonical-parent projected endpoint
route.  So the benchmark now separates graph-level theorem-4.9 positivity not only from the live
same-embedding sufficient shells, but from both concrete same-embedding projected source routes
already formalized in Lean.  The same projected-route wheel obstruction now also retains the
explicit local two-interior-edge burden through
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_and_twoDistinctInteriorEdgesOnFaceBoundary_without_sameEmbedding_projectedSourceRoutes`.
So even this route-level projected-endpoint failure is now packaged together with the concrete
local reason that blocks the facewise-at-most-one / canonical-choice branch on the same fixed
embedding, not only as a coarse failed pair of projected-source routes.  The new theorem
`wheelWithInnerTriangleGraph_explicitTait_graphLevelSynthesis_with_fixedEmbedding_without_replacementPositiveProjectedGeometry_or_previousBoundaryWitness`
extends that same graph-vs-fixed-embedding separation to the newer repaired positive route as
well: the graph still admits full theorem-4.9 synthesis on some embedding, but on the honest
source-preserving wheel embedding the same explicit Tait coloring, honest source, and surviving
purified carrier still fail both direct replacement-positive packages and the repaired
previous-boundary witness geometry.  So current graph-level positivity on this benchmark remains
strictly upstream of every same-embedding positive route surface now formalized around the live
annulus manuscript lane.

`Theorem49ResidualBoundaryObstruction.lean` then calibrates that gap on the live
shared-interior-pair source benchmark.  The theorems
`not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair`,
`not_nonempty_residualBoundarySelectorData_sharedInteriorPair`, and
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that honest closed-walk source data, a Tait coloring, and `HasUnblockedInteriorEndpoint`
still do not force any of the natural residual same-embedding packages introduced in this pass.
The same residual obstruction now reaches the stronger exact one-collar/v23 shell too:
`exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_naturalResidualSameEmbeddingGeometry_sharedInteriorPair`,
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`,
and the successor-cycle analogues show that even exact one-collar current-boundary data plus a
real v23 residual initial state still do not force residual-boundary witness data, residual
selector data, or even the raw height-ordered/collar-layer witness-cover packages on that same
shared-interior-pair embedding.
Constructively, `Theorem49ResidualBoundaryRoute.lean` now also lowers the same exact
one-collar/v23 rooted shared-edge face-membership shell, once paired with
`HasUnblockedInteriorEndpoint`, to the named root-distance positive route surfaces and hence to
the projected nonempty and raw quotient/error theorem-4.9 endpoints on both the honest
closed-walk and successor-cycle shells.  So that exact shell no longer appears in Lean only as a
direct full-synthesis shortcut; it now enters the modular replacement-positive pipeline at the
same route-facing interfaces used elsewhere.
The same route file now also lowers those named root-distance positive route surfaces to
`Theorem49ResidualBoundaryPositiveProjectedGeometryOn` and the corresponding current-boundary
remainder witness interface.  So the exact one-collar/v23 rooted-cover shell now reaches the
residual-boundary positive lane by composition as well, not only the projected theorem-4.9
endpoint lane.
`Theorem49ResidualBoundaryPeeling.lean` now also proves the same residual bridge directly from
the rooted shared-edge face-membership cover itself on both the honest closed-walk and
successor-cycle shells, and `Theorem49ResidualBoundaryRoute.lean` adds the matching exact
one-collar/v23 wrappers.  So the exact rooted-cover shell no longer needs an explicit detour
through a named root-distance package just to expose residual-positive geometry or a
current-boundary remainder witness; those surfaces are available there directly as well.
The same route file now also packages those direct exact-shell residual consequences at graph
level: from existential one-collar/v23 rooted-cover data plus `HasUnblockedInteriorEndpoint`, it
now directly derives existential residual-positive geometry and existential current-boundary
remainder witnesses on both the honest closed-walk and successor-cycle shells.  So downstream
route consumers no longer need to rebuild that existential residual plumbing by hand once they
start from the live exact shell.
The same exact rooted-cover shell now also has matching graph-level theorem-4.9 endpoint
packaging: existential one-collar/v23 rooted-cover data plus `HasUnblockedInteriorEndpoint`
directly yields existential `Theorem49BoundaryRootNonemptyProjectedSynthesis` and existential
`Theorem49BoundaryRawQuotientErrorPackage` on both the honest closed-walk and successor-cycle
shells.  So the exact rooted-cover lane now exports both the residual interface and the theorem-
4.9 endpoint interface without further existential repackaging.
At the more generic residual layer-face witness level, the peeling and route files now also expose
the raw quotient/error theorem-4.9 endpoint directly: same-embedding witness data plus
`HasUnblockedInteriorEndpoint` yields `Theorem49BoundaryRawQuotientErrorPackage`, and the honest
closed-walk / successor-cycle existential shells now package that endpoint at graph level too.
So the residual witness layer itself now exports the full theorem-4.9 endpoint pair, not only the
root-synthesis and projected-nonempty half.
The selector shell now matches that route-facing endpoint coverage too.  Starting from honest
closed-walk or successor-cycle source data on a fixed embedding, same-embedding
`ResidualBoundarySelectorData` now exports `Theorem49BoundaryRootSynthesis`,
`Theorem49BoundaryRootNonemptyProjectedSynthesis`, and `Theorem49BoundaryRawQuotientErrorPackage`;
and the route file also packages all three at graph level under the corresponding existential
closed-walk / successor-cycle selector shells.  So downstream work can now use the selector lane
as a full theorem-4.9 endpoint interface rather than only as a source of root synthesis.
The residual interface is now exposed at that same boundary-order layer too.  Honest closed-walk
or successor-cycle source data paired with either same-embedding residual witness data or
same-embedding `ResidualBoundarySelectorData`, together with `HasUnblockedInteriorEndpoint`, now
directly exports `Theorem49ResidualBoundaryPositiveProjectedGeometryOn` and the corresponding
current-boundary remainder witness on the same embedding; and the route file packages both
consequences at graph level for all four shells.  So both the residual witness lane and the
selector lane now expose not only theorem-4.9 endpoints but also the upstream residual-positive
interface used elsewhere in the live route.
The same graph-level residual export is now available one layer more generally too: if an exact
one-collar/v23 shell already carries same-embedding
`InteriorDualBoundaryRootAdjDistancePeelData` plus `HasUnblockedInteriorEndpoint`, then the route
file now directly packages existential residual-positive geometry and existential
current-boundary remainder witnesses on both the honest closed-walk and successor-cycle shells.
So once downstream work proves the generic adj-distance package on some live exact-shell witness,
it can enter the residual interface without any additional existential repackaging.
So v23.5 has gained a formal residual interface and a sharper negative benchmark family, but not
yet a completed constructive proof route.

-/

end Mettapedia.GraphTheory.FourColor
