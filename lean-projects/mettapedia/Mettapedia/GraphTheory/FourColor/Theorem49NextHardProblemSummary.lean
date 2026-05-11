import Mettapedia.GraphTheory.FourColor.Theorem49DerivationImpossibilitySummary
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometry
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusWitnessRegression
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestGeometryRegression
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceCanonicalWitness
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacement
import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryFreeSelectorPositiveRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacementRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceConstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacementRegression

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
     constructs both the height-ordered and finite-collar replacement packages and reaches
     `Theorem49BoundaryRootNonemptyProjectedSynthesis`; the route file adds the closed-walk
     traceability theorem
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint`
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
     height-ordered geometry, finite-collar geometry, and the projected synthesis endpoint, with
     closed-walk and successor-cycle source-facing wrappers
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
same source boundary split.

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
For constructive use, the same route file now has direct closed-walk and successor-cycle
projected-synthesis theorems from `HasUnblockedInteriorEndpoint`, so the carrier side of future
positive source examples can be supplied by a local endpoint witness instead of an already
packaged carrier set.

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
     and its successor-cycle counterpart.
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
     surfaces for callers that already have the derived field.
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
     `theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector`
     composes the same source-fixed parent hypotheses through the selector-to-construction
     surface directly.  This selector route now also has the downstream route-facing forms
     `theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_via_boundaryFreeSelector`
     and
     `exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint_via_boundaryFreeSelector`,
     so graph-level source data plus the local endpoint witness can use the selector path
     without first repackaging the carrier as raw selected-boundary nonemptiness.
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
     `Theorem49PlanarBoundaryAnnulusRootInteriorDualObstructionRegression.lean` now instantiates
     that source-side obstruction on the concrete two-band triangular annulus
     `twoBandAnnulusGraph`: it proves the honest closed-walk source package
     `twoBandClosedWalkAnnulusBoundarySource`, the outer-to-inner interior-dual adjacency
     `twoBandAnnulus_interiorDual_adj_outer0_inner0`, and the concrete nonexistence theorem
     `not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_twoBandAnnulus_via_source_reachability`.
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
     sufficiency branch either.
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

What this pass now **does** establish is a same-embedding lowering from stronger source-side
canonical-parent cover data.  `Theorem49ResidualBoundaryPeeling.lean` proves
`theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint`,
`theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary`,
and the corresponding successor-cycle wrappers.  `Theorem49PositiveGeometricSourceReplacementRoute.lean`
and `Theorem49BoundaryFreeSelectorPositiveRoute.lean` supply the same direct lowering to the
generic parent and boundary-free-selector theorem-4.9 endpoints.  So the downstream side of this
stronger source-fixed canonical-parent raw-cover package is now completely explicit.

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

So the parent, selector, and residual theorem-4.9 lowerings from the raw canonical-parent cover
package are now calibrated as vacuous on the current live endpoint semantics.  The remaining live
question is no longer how to derive that package together with `HasUnblockedInteriorEndpoint`
from honest source data or from the exact v23 seed.  Even before any live carrier is added, the
same raw-cover shell has already collapsed to the no-interior-edge branch.  So the route must
either change the source interface / endpoint notion or prove impossibility directly on the live
shell.

The obstruction file now ties that gap directly to the exact v23 algebraic seed.
`nonempty_sharedInteriorPair_v23ResidualBoundaryInitialState_sipFace0Boundary` builds
`V23ResidualBoundaryInitialState` on an actual shared-interior-pair face boundary, while
`sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_residualBoundaryGeometry`
and
`not_forall_residualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that even this exact Step 2 initial state, together with honest closed-walk source data, a
Tait coloring, and `HasUnblockedInteriorEndpoint`, still does not force any residual positive
geometry on the same embedding.

The same benchmark now also blocks the stronger upstream source-fixed raw-cover shell itself.
`sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover`
packages the exact Step 2 seed together with failure of the closed-walk raw canonical-parent
shared-edge-cover package on that same embedding, and
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
shows that no universal theorem of the form “honest source + Tait + endpoint + exact v23 seed
forces some source-fixed raw canonical-parent cover witness” can hold.

The same exact seed now fails even to recover the weaker degenerate branch to which that raw-cover
shell collapses.  The theorem
`sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsNoInteriorEdges`
packages the exact Step 2 seed together with failure of the closed-walk root-cover plus
`interiorEdgeSupport = ∅` shell itself, and
`not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
shows that no universal theorem of the form “honest source + Tait + endpoint + exact v23 seed
forces some no-interior-edge boundary-root witness” can hold either.

The same exact seed also fails already at the strictly weaker local boundary-free-selector
surface.  The theorem
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
coloring, and `HasUnblockedInteriorEndpoint` still do not force residual positive geometry.
The stronger route-facing raw-cover shell is now blocked too:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsCanonicalParentSharedEdgeCover_sharedInteriorPair`
and
`not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that successor-cycle boundary-order data plus the exact v23 seed still do not force even the
raw canonical-parent shared-edge-cover shell on the same embedding.

The same successor-cycle shell also fails already at the weaker degenerate source branch:
`exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_and_v23ResidualBoundaryInitialState_without_boundaryFaceRootsNoInteriorEdges_sharedInteriorPair`
and
`not_forall_some_successorCycleBoundaryFaceRootsNoInteriorEdges_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that the exact seed does not even force the route-facing boundary-root plus
`interiorEdgeSupport = ∅` shell on the same embedding.

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
annulus-collar geometry on the same embedding.  The failed universals
`not_forall_some_knownSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
and
`not_forall_some_knownSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_v23ResidualBoundaryInitialState_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that this gap already persists on both the honest closed-walk and the actual successor-cycle
boundary-order shells.  So the missing v23.5 theorem is not a way to re-enter one of the older
same-embedding geometry ladders, or even to recover the upstream raw-cover shell, from the exact
Step~2 algebraic seed, or even its boundary-free-selector / degenerate no-interior-edge shadows;
it is a genuinely new source-to-residual geometric bridge or live-boundary cancellation
certificate.

At the same time, the exact Step~2 seed is not globally incompatible with the degenerate
source-fixed no-interior branch.  The new module
`Theorem49ResidualBoundaryPositiveRegression.lean` equips the existing two-triangle no-interior
source with a proper nonzero Tait edge coloring `twoTriangleTaitEdgeColoring`, proves
`nonempty_twoTriangleOuterFace_v23ResidualBoundaryInitialState`, and then packages the same exact
seed together with the honest closed-walk source, the root-cover / root-separation facts, empty
`interiorEdgeSupport`, the resulting
`InteriorDualBoundaryRootParentPeelData`, and even a
`BoundaryFreeIncidentFaceSelector` on that embedding.  So the shared-interior-pair exact-seed
obstructions are not exposing an outright incompatibility between v23 Step~2 algebra and the
degenerate no-interior source surfaces; they isolate a genuine non-forcing gap on the live
endpoint benchmark.

`Theorem49ResidualBoundaryObstruction.lean` then calibrates that gap on the live
shared-interior-pair source benchmark.  The theorems
`not_nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_sharedInteriorPair`,
`not_nonempty_residualBoundarySelectorData_sharedInteriorPair`, and
`not_forall_some_naturalResidualSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_sharedInteriorPair`
show that honest closed-walk source data, a Tait coloring, and `HasUnblockedInteriorEndpoint`
still do not force any of the natural residual same-embedding packages introduced in this pass.
So v23.5 has gained a formal residual interface and a sharper negative benchmark family, but not
yet a completed constructive proof route.

-/

end Mettapedia.GraphTheory.FourColor
