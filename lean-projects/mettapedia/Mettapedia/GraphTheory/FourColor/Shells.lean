import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
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
