import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorFamilyPairing
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices
import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundaryRoute

/-!
# Bundled hypothesis shells for the Theorem 4.9 route

The route literature accumulated theorem statements quantifying over 8–10
separate hypotheses ("shells"): a source presentation, exact one-collar
current-boundary data on the same boundary split, a Tait coloring, the local
unblocked-endpoint witness, and an exact v23 residual seed.  This file bundles
those telescopes into named structures so that frontier statements
(`Mettapedia.GraphTheory.FourColor.Frontier`) can be written and read at a
glance.

Nothing here adds or removes logical strength: each bundle is definitionally
the tuple of its fields, and `Frontier` proves the equivalences with the
historical unbundled statements by direct destructuring.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Exact one-collar current-boundary data whose underlying annulus boundary
split is a prescribed one.  This is the strongest current-boundary repair that
honest sources are known to supply for free
(`exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource`). -/
structure ExactOneCollarOn (emb : PlaneEmbeddingWithBoundary G)
    (boundary : PlanarBoundaryAnnulusBoundaryData emb) where
  current : PlanarBoundaryAnnulusCurrentBoundaryData emb
  numCollars_eq_one : current.numCollars = 1
  boundary_eq : current.toPlanarBoundaryAnnulusBoundaryData = boundary

/-- A real Tait coloring together with an exact v23 residual boundary initial
state for a chosen color pair and face boundary.  The residual state is
unconditionally constructible (see `TaitV23Data.ofTait`), so the genuine
content of this bundle is the Tait coloring itself; the seed fields are kept
because the manuscript's Step 2 statements quantify over them. -/
structure TaitV23Data (G : SimpleGraph V) where
  coloring : G.EdgeColoring Color
  isTait : IsTaitEdgeColoring G coloring
  a : Color
  b : Color
  faceBoundary : Finset G.edgeSet
  v23 : Nonempty (V23ResidualBoundaryInitialState coloring a b faceBoundary)

/-- Any Tait coloring yields the full v23 bundle for any color pair and face
boundary, because the exact v23 Step 2 purification is already proved. -/
def TaitV23Data.ofTait (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (a b : Color) (faceBoundary : Finset G.edgeSet) : TaitV23Data G :=
  ⟨C, hC, a, b, faceBoundary,
    ⟨residualBoundaryInitialState_of_sum_v23_single_component_purifications_eq_boundaryOnlyGenerator
      C a b faceBoundary⟩⟩

/-- The endpoint-bearing exact one-collar/v23 shell over the honest closed-walk
source presentation.  This is the strongest hypothesis package on the
closed-walk branch that is currently known *not* to force the missing
same-embedding geometry (see `Frontier`). -/
structure ClosedWalkExactShell (emb : PlaneEmbeddingWithBoundary G) where
  source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb
  oneCollar : ExactOneCollarOn emb source.toPlanarBoundaryAnnulusBoundaryData
  tait : TaitV23Data G
  endpoint : HasUnblockedInteriorEndpoint emb

/-- The exact closed-walk shell together with the non-geometric algebraic
cancellation certificate suggested by the finite lab: every nonzero
selected-boundary-zero chain pairs nontrivially with some projected
Definition 4.8 generator for the shell's Tait coloring. -/
structure ClosedWalkCancellationShell (emb : PlaneEmbeddingWithBoundary G)
    [Fintype G.edgeSet] where
  exactShell : ClosedWalkExactShell emb
  detector : BoundaryZeroProjectedGeneratorDetector emb exactShell.tait.coloring

/-- The exact closed-walk shell together with a smaller explicit projected-generator detector on
some coloring family inside the shell Tait coloring's edge-Kempe closure.  This matches the
finite-lab certificate shape more closely than the closure-wide detector. -/
structure ClosedWalkNeighborhoodCancellationShell (emb : PlaneEmbeddingWithBoundary G)
    [Fintype G.edgeSet] where
  exactShell : ClosedWalkExactShell emb
  colorings : Set (G.EdgeColoring Color)
  subset_closure : colorings ⊆ G.EdgeKempeClosure exactShell.tait.coloring
  detector : BoundaryZeroProjectedColoringGeneratorDetector emb colorings

/-- The exact closed-walk shell together with an explicit projected-generator family inside the
shell Tait coloring's Kempe closure whose concrete family-evaluation pairing map has trivial
kernel.  This packages the direct kernel-checkable finite `F₂` certificates suggested by the
current lab output. -/
structure ClosedWalkNeighborhoodPairingKernelShell (emb : PlaneEmbeddingWithBoundary G)
    [Fintype G.edgeSet] where
  exactShell : ClosedWalkExactShell emb
  colorings : Set (G.EdgeColoring Color)
  subset_closure : colorings ⊆ G.EdgeKempeClosure exactShell.tait.coloring
  κ : Type*
  family : κ → projectedColoringGeneratorSubspace emb colorings
  pairingKernel_eq_bot :
    LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥

/-- The endpoint-bearing exact one-collar/v23 shell over the successor-cycle
boundary-order presentation. -/
structure SuccessorCycleExactShell (emb : PlaneEmbeddingWithBoundary G) where
  boundaryReachability : PlanarBoundaryAnnulusBoundaryReachabilityData emb
  dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb
  selectedBoundaryArc :
    (f : AmbientFace emb.faces) →
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f
  oneCollar : ExactOneCollarOn emb boundaryReachability.toPlanarBoundaryAnnulusBoundaryData
  tait : TaitV23Data G
  endpoint : HasUnblockedInteriorEndpoint emb

/-- Successor-cycle version of the exact shell plus algebraic cancellation
certificate. -/
structure SuccessorCycleCancellationShell (emb : PlaneEmbeddingWithBoundary G)
    [Fintype G.edgeSet] where
  exactShell : SuccessorCycleExactShell emb
  detector : BoundaryZeroProjectedGeneratorDetector emb exactShell.tait.coloring

/-- Successor-cycle version of the exact shell plus an explicit subfamily detector. -/
structure SuccessorCycleNeighborhoodCancellationShell (emb : PlaneEmbeddingWithBoundary G)
    [Fintype G.edgeSet] where
  exactShell : SuccessorCycleExactShell emb
  colorings : Set (G.EdgeColoring Color)
  subset_closure : colorings ⊆ G.EdgeKempeClosure exactShell.tait.coloring
  detector : BoundaryZeroProjectedColoringGeneratorDetector emb colorings

/-- Successor-cycle version of the exact shell plus a direct family-pairing kernel certificate. -/
structure SuccessorCycleNeighborhoodPairingKernelShell (emb : PlaneEmbeddingWithBoundary G)
    [Fintype G.edgeSet] where
  exactShell : SuccessorCycleExactShell emb
  colorings : Set (G.EdgeColoring Color)
  subset_closure : colorings ⊆ G.EdgeKempeClosure exactShell.tait.coloring
  κ : Type*
  family : κ → projectedColoringGeneratorSubspace emb colorings
  pairingKernel_eq_bot :
    LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥

/-- Forget the stronger family-kernel certificate down to the smaller-family detector shell. -/
def ClosedWalkNeighborhoodPairingKernelShell.toClosedWalkNeighborhoodCancellationShell
    {emb : PlaneEmbeddingWithBoundary G} [Fintype G.edgeSet]
    (shell : ClosedWalkNeighborhoodPairingKernelShell emb) :
    ClosedWalkNeighborhoodCancellationShell emb where
  exactShell := shell.exactShell
  colorings := shell.colorings
  subset_closure := shell.subset_closure
  detector :=
    detector_of_ker_planarBoundaryZeroFamilyPairingMap_eq_bot
      shell.family shell.pairingKernel_eq_bot

/-- Lower the successor-cycle shell to the honest closed-walk shell.  The
boundary split of the lowered source is definitionally the reachability
split, so the exact one-collar data transports unchanged. -/
def SuccessorCycleExactShell.toClosedWalkExactShell
    {emb : PlaneEmbeddingWithBoundary G} (shell : SuccessorCycleExactShell emb) :
    ClosedWalkExactShell emb where
  source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      shell.boundaryReachability shell.dartCycles shell.selectedBoundaryArc
  oneCollar := shell.oneCollar
  tait := shell.tait
  endpoint := shell.endpoint

/-- Lower the successor-cycle cancellation shell to the honest closed-walk
version.  The detector certificate is preserved unchanged because the lowered
shell keeps the same embedding and Tait coloring. -/
def SuccessorCycleCancellationShell.toClosedWalkCancellationShell
    {emb : PlaneEmbeddingWithBoundary G} [Fintype G.edgeSet]
    (shell : SuccessorCycleCancellationShell emb) :
    ClosedWalkCancellationShell emb where
  exactShell := shell.exactShell.toClosedWalkExactShell
  detector := shell.detector

/-- Lower the successor-cycle neighborhood-cancellation shell to the honest closed-walk version.
The explicit family and its detector transport unchanged because the lowered shell keeps the same
embedding and Tait coloring. -/
def SuccessorCycleNeighborhoodCancellationShell.toClosedWalkNeighborhoodCancellationShell
    {emb : PlaneEmbeddingWithBoundary G} [Fintype G.edgeSet]
    (shell : SuccessorCycleNeighborhoodCancellationShell emb) :
    ClosedWalkNeighborhoodCancellationShell emb where
  exactShell := shell.exactShell.toClosedWalkExactShell
  colorings := shell.colorings
  subset_closure := by
    simpa using shell.subset_closure
  detector := shell.detector

/-- Lower the successor-cycle pairing-kernel shell to the honest closed-walk version.  The
explicit family and its kernel certificate transport unchanged because the lowered shell keeps the
same embedding and Tait coloring. -/
def SuccessorCycleNeighborhoodPairingKernelShell.toClosedWalkNeighborhoodPairingKernelShell
    {emb : PlaneEmbeddingWithBoundary G} [Fintype G.edgeSet]
    (shell : SuccessorCycleNeighborhoodPairingKernelShell emb) :
    ClosedWalkNeighborhoodPairingKernelShell emb where
  exactShell := shell.exactShell.toClosedWalkExactShell
  colorings := shell.colorings
  subset_closure := by
    simpa using shell.subset_closure
  κ := shell.κ
  family := shell.family
  pairingKernel_eq_bot := by
    simpa using shell.pairingKernel_eq_bot

/-- Generic refutation schema: one explicit witness of a shell that fails a
target refutes every universal derivation of that target from that shell.
All of the historical "reusable witness-based converse" theorems are
instances of this lemma applied to a bundled shell. -/
theorem not_forall_target_of_exists_shell_witness {ι : Sort*}
    {Shell Target : ι → Prop} (h : ∃ i, Shell i ∧ ¬ Target i) :
    ¬ ∀ i, Shell i → Target i := by
  rcases h with ⟨i, hShell, hNotTarget⟩
  exact fun hAll => hNotTarget (hAll i hShell)

end Mettapedia.GraphTheory.FourColor
