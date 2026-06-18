import Mettapedia.GraphTheory.FourColor.Shells
import Mettapedia.GraphTheory.FourColor.Theorem49DetectorStrength
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceRoute
import Mettapedia.GraphTheory.FourColor.Theorem49AtMostOneNonemptyCarrierImpossibility
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacementRoute
import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49PlanarBoundaryAnnulusWheelWitnessRegression
import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49ForcingInteriorEdgeObstructionRegression
import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49PositiveGeometricSourceReplacementRegression

/-!
# The current Theorem 4.9 frontier

This file states, over the bundled shells of
`Mettapedia.GraphTheory.FourColor.Shells`, the *maximal* results of the route
audit — the strongest hypothesis packages known not to force the missing
geometry, and the weakest geometric inputs known to force the full
Theorem 4.9 synthesis endpoint.  Everything is a thin wrapper around theorems
proved elsewhere (live route files and the `Legacy` ledger); no new
mathematics happens here.

## The picture

Positive (sufficiency, live route files):
* a `ClosedWalkExactShell` together with repaired previous-boundary witness
  geometry, OR explicit well-founded peel-witness data, OR generic
  interior-dual boundary-root distance-peel data, OR the non-geometric
  projected-generator detector certificate, OR a direct explicit-family
  pairing-kernel certificate, reaches full `Theorem49BoundaryRootSynthesis`.

Negative (maximal refuted shells, `Legacy` benchmarks):
* the wheel-with-inner-triangle inhabits both exact shells while refuting
  generic `InteriorDualBoundaryRootAdjDistancePeelData`;
* the shared-interior-pair inhabits the closed-walk exact shell while
  refuting all four replacement-positive geometry packages;
* every closed-walk shell with an unblocked endpoint must put two distinct
  interior edges on some face boundary, which forbids the facewise
  at-most-one, canonical-choice, and source-preserving one-collar repairs.

So the single open question is exactly the gap between the shells and the
geometric inputs.  More precisely, `Theorem49DetectorStrength.lean` now proves
that on every shell-bearing embedding the full selected-boundary-zero space is
already strictly larger than the theorem-4.9 target `W₀(H)`, so the new
detector/cancellation oracle really is stronger than the manuscript target,
not a mere restatement.  See `ROADMAP.md`.
-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression
open Theorem49ForcingInteriorEdgeObstructionRegression
open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
open Theorem49PositiveGeometricSourceReplacementRegression

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-! ## Positive lane: what suffices for the synthesis endpoint -/

/-- Repaired previous-boundary witness geometry on the shell's embedding closes
the route: full Theorem 4.9 synthesis for the shell's Tait coloring. -/
theorem boundaryRootSynthesis_of_closedWalkExactShell_and_previousBoundaryWitnessGeometry
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (geometry : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
    shell.source geometry shell.endpoint shell.tait.coloring shell.tait.isTait

/-- Explicit well-founded face-peel witness data also closes the route. -/
theorem boundaryRootSynthesis_of_closedWalkExactShell_and_wellFoundedPeelWitnessData
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_wellFoundedFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    shell.source data shell.endpoint shell.tait.coloring shell.tait.isTait

/-- Generic interior-dual boundary-root distance-peel data closes the route:
it constructs the well-founded witness cover on the shell's own embedding. -/
theorem boundaryRootSynthesis_of_closedWalkExactShell_and_interiorDualPeelData
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (peel : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkExactShell_and_wellFoundedPeelWitnessData shell
    (planarBoundaryWellFoundedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      shell.source peel)

/-- The finite-lab algebraic cancellation certificate also closes the route:
once the shell's Tait coloring satisfies the projected-generator detector
property, no additional theorem-4.9 algebra remains. -/
theorem boundaryRootSynthesis_of_closedWalkExactShell_and_boundaryZeroProjectedGeneratorDetector
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (detector : BoundaryZeroProjectedGeneratorDetector emb shell.tait.coloring) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedGeneratorDetector
    emb shell.tait.coloring detector

/-- Bundled closed-walk form of the algebraic cancellation route. -/
theorem boundaryRootSynthesis_of_closedWalkCancellationShell
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkCancellationShell emb) :
    Theorem49BoundaryRootSynthesis emb shell.exactShell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkExactShell_and_boundaryZeroProjectedGeneratorDetector
    shell.exactShell shell.detector

/-- Smaller explicit projected-generator certificates inside the shell Tait coloring's Kempe
closure also close the route.  This is the live surface form that matches the finite-lab
certificate shape directly. -/
theorem boundaryRootSynthesis_of_closedWalkExactShell_and_boundaryZeroProjectedColoringGeneratorDetector
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    (detector : BoundaryZeroProjectedColoringGeneratorDetector emb colorings) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedColoringGeneratorDetector
    emb shell.tait.coloring colorings hsubset detector

/-- Bundled closed-walk form of the smaller-family algebraic cancellation route. -/
theorem boundaryRootSynthesis_of_closedWalkNeighborhoodCancellationShell
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkNeighborhoodCancellationShell emb) :
    Theorem49BoundaryRootSynthesis emb shell.exactShell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkExactShell_and_boundaryZeroProjectedColoringGeneratorDetector
    shell.exactShell shell.colorings shell.subset_closure shell.detector

/-- Direct family-pairing kernel certificates on an explicit Kempe neighborhood also close the
route.  This is the exact shell-facing form of the current finite `F₂` kernel-check target. -/
theorem boundaryRootSynthesis_of_closedWalkExactShell_and_familyPairingKerEqBot
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (hker : LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  theorem49BoundaryRootSynthesis_of_familyPairingKerEqBot
    emb shell.tait.coloring colorings hsubset family hker

/-- Bundled closed-walk form of the explicit family-pairing kernel route. -/
theorem boundaryRootSynthesis_of_closedWalkNeighborhoodPairingKernelShell
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkNeighborhoodPairingKernelShell emb) :
    Theorem49BoundaryRootSynthesis emb shell.exactShell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkNeighborhoodCancellationShell
    shell.toClosedWalkNeighborhoodCancellationShell

/-- Successor-cycle form of the interior-dual sufficiency. -/
theorem boundaryRootSynthesis_of_successorCycleExactShell_and_interiorDualPeelData
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : SuccessorCycleExactShell emb)
    (peel : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    Theorem49BoundaryRootSynthesis emb shell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkExactShell_and_interiorDualPeelData
    shell.toClosedWalkExactShell peel

/-- Successor-cycle form of the algebraic cancellation sufficiency. -/
theorem boundaryRootSynthesis_of_successorCycleCancellationShell
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : SuccessorCycleCancellationShell emb) :
    Theorem49BoundaryRootSynthesis emb shell.exactShell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkCancellationShell
    shell.toClosedWalkCancellationShell

/-- Successor-cycle form of the smaller-family algebraic cancellation route. -/
theorem boundaryRootSynthesis_of_successorCycleNeighborhoodCancellationShell
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G} (shell : SuccessorCycleNeighborhoodCancellationShell emb) :
    Theorem49BoundaryRootSynthesis emb shell.exactShell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkNeighborhoodCancellationShell
    shell.toClosedWalkNeighborhoodCancellationShell

/-- Successor-cycle form of the direct family-pairing kernel route. -/
theorem boundaryRootSynthesis_of_successorCycleNeighborhoodPairingKernelShell
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : SuccessorCycleNeighborhoodPairingKernelShell emb) :
    Theorem49BoundaryRootSynthesis emb shell.exactShell.tait.coloring :=
  boundaryRootSynthesis_of_closedWalkNeighborhoodPairingKernelShell
    shell.toClosedWalkNeighborhoodPairingKernelShell

/-! ## Structural necessity: why the cardinal repairs are dead -/

/-- On every closed-walk exact shell, the theorem-4.9 target `W₀(H)` is a
proper subspace of the full selected-boundary-zero chain space.  This is the
route-facing form of the detector-strength gap: the new cancellation oracle is
strictly stronger than the manuscript target on every shell-bearing
embedding. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_lt_planarBoundaryZeroSubmodule_of_closedWalkExactShell
    [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb) :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) <
      planarBoundaryZeroSubmodule emb :=
  theorem49BoundaryZeroKirchhoffSubspace_lt_planarBoundaryZeroSubmodule_of_hasUnblockedInteriorEndpoint
    shell.endpoint

/-- Every closed-walk shell (the endpoint witness suffices) forces two distinct
interior edges onto some face boundary.  This is the structural fact that kills
the facewise at-most-one, canonical witness choice, and source-preserving
one-collar repair lanes: they all imply the opposite. -/
theorem exists_two_distinct_interiorEdges_of_closedWalkExactShell
    {emb : PlaneEmbeddingWithBoundary G} (shell : ClosedWalkExactShell emb) :
    ∃ f : AmbientFace emb.faces,
      ∃ e₁ : G.edgeSet,
        e₁ ∈ emb.faceBoundary f.1 ∧
          e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ∃ e₂ : G.edgeSet,
              e₂ ∈ emb.faceBoundary f.1 ∧
                e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧ e₁ ≠ e₂ :=
  exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint
    shell.source shell.endpoint

/-! ## Negative lane: maximal shells that do not force the geometry -/

/-- The wheel-with-inner-triangle inhabits the full closed-walk exact shell
while refuting generic interior-dual distance-peel data.  This is the maximal
closed-walk obstruction: the shell sits strictly below the geometric layer. -/
theorem exists_closedWalkExactShell_without_interiorDualPeelData_wheel :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      Nonempty (ClosedWalkExactShell emb) ∧
        ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
          emb.faces emb.faceBoundary) := by
  obtain ⟨data, hnum, hboundary⟩ :=
    exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
      wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
  refine ⟨wheelWithInnerTriangleEmbedding, ⟨?_⟩,
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩
  exact
    { source := wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
      oneCollar := ⟨data, hnum, hboundary⟩
      tait :=
        TaitV23Data.ofTait wheelWithInnerTriangleTaitEdgeColoring
          wheelWithInnerTriangleTaitEdgeColoring_isTait red blue
          (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
      endpoint := hasUnblockedInteriorEndpoint_wheelWithInnerTriangle }

/-- Bundled form of the failed universal converse on the closed-walk branch:
no derivation can pass from the exact shell to generic interior-dual
distance-peel data. -/
theorem not_forall_interiorDualPeelData_of_closedWalkExactShell_wheel :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Nonempty (ClosedWalkExactShell emb) →
          Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
            emb.faces emb.faceBoundary) :=
  not_forall_target_of_exists_shell_witness
    exists_closedWalkExactShell_without_interiorDualPeelData_wheel

/-- The same maximal obstruction on the successor-cycle boundary-order
presentation. -/
theorem exists_successorCycleExactShell_without_interiorDualPeelData_wheel :
    ∃ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
      Nonempty (SuccessorCycleExactShell emb) ∧
        ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
          emb.faces emb.faceBoundary) := by
  obtain ⟨data, hnum, hboundary⟩ :=
    exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        wheelWithInnerTriangleAnnulusBoundaryReachabilityData
        wheelWithInnerTriangleDartSuccessorCycleGeometry
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace)
  refine ⟨wheelWithInnerTriangleEmbedding, ⟨?_⟩,
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_wheelWithInnerTriangle_via_forcingInteriorEdgeWitness⟩
  exact
    { boundaryReachability := wheelWithInnerTriangleAnnulusBoundaryReachabilityData
      dartCycles := wheelWithInnerTriangleDartSuccessorCycleGeometry
      selectedBoundaryArc :=
        wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      oneCollar := ⟨data, hnum, hboundary⟩
      tait :=
        TaitV23Data.ofTait wheelWithInnerTriangleTaitEdgeColoring
          wheelWithInnerTriangleTaitEdgeColoring_isTait red blue
          (wheelWithInnerTriangleEmbedding.faceBoundary wheelFace0.1)
      endpoint := hasUnblockedInteriorEndpoint_wheelWithInnerTriangle }

/-- Bundled failed universal converse on the successor-cycle branch. -/
theorem not_forall_interiorDualPeelData_of_successorCycleExactShell_wheel :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Nonempty (SuccessorCycleExactShell emb) →
          Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
            emb.faces emb.faceBoundary) :=
  not_forall_target_of_exists_shell_witness
    exists_successorCycleExactShell_without_interiorDualPeelData_wheel

/-- The shared-interior-pair benchmark inhabits the closed-walk exact shell
while refuting all four replacement-positive geometry packages at once.  So
the shell also sits strictly below every current sufficient same-embedding
geometry surface. -/
theorem exists_closedWalkExactShell_without_replacementPositiveGeometry_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      Nonempty (ClosedWalkExactShell emb) ∧
        ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∧
        ¬ Theorem49CollarLayerPositiveProjectedGeometryOn emb ∧
        ¬ Theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn emb ∧
        ¬ Theorem49SuccessorCycleAnnulusCollarPositiveProjectedGeometryOn emb := by
  obtain ⟨emb, source, ⟨data, hnum, hboundary⟩, ⟨C, hC⟩, hEndpoint, h₁, h₂, h₃, h₄⟩ :=
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_hasUnblockedInteriorEndpoint_without_any_replacementPositiveProjectedGeometryOn_sharedInteriorPair
  exact
    ⟨emb,
      ⟨{ source := source
         oneCollar := ⟨data, hnum, hboundary⟩
         tait := TaitV23Data.ofTait C hC red blue ∅
         endpoint := hEndpoint }⟩,
      h₁, h₂, h₃, h₄⟩

end Mettapedia.GraphTheory.FourColor
