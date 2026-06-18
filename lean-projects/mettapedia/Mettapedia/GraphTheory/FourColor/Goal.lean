import Mettapedia.GraphTheory.FourColor.Frontier

/-!
# The goal of the FourColor development

This file states what the development is actually for, in dependency order,
so that the target is visible without reading the route files.

## Context (informal)

By Tait's classical reduction, the Four Color Theorem is equivalent to: every
bridgeless cubic planar graph admits a proper 3-edge-coloring
(`IsTaitEdgeColoring`).  Goertzel's manuscript route attacks this through an
inductive boundary argument: Theorem 4.9 of the v23 manuscript claims an
algebraic synthesis (`Theorem49BoundaryRootSynthesis`) — Kirchhoff boundary
algebra spanned by projected Kempe-closure generators — for plane embeddings
with boundary carrying suitable source data.  Tait's reduction itself is not
formalized in this development; the formal work targets the manuscript's
Theorem 4.9 layer, where the audit located the load-bearing gap.

## What this file proves

`Theorem49ShellClaim` is the manuscript-shaped target: synthesis on every
embedding carrying the bundled exact shell.  It follows from any of four
uniform geometric oracles (previous-boundary witness geometry, well-founded
peel-witness data, interior-dual distance-peel data, or the v23.5
residual/current-boundary positive wrapper), or from non-geometric algebraic
cancellation oracles stated either in the projected-generator detector form
or in the more certificate-faithful direct kernel-check form exposed by the
finite lab.  The four geometric oracles are all provably false, by the
benchmark embeddings that inhabit the shell while refuting the geometry.  The
fourth refutation is the formal answer to the v23.5 revision memo: the
residual lane's current positive wrapper is fixed-embedding equivalent to the
collar-layer surface
(`theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn`),
so it inherits the same benchmark refutation; the proposed repair is
conservative, not a workaround.  So the manuscript route survives only if
either real same-embedding geometry, strictly stronger than everything the
exact shell supplies, is constructed from hypotheses the benchmarks do not
satisfy; or a genuinely non-geometric shell-wise algebraic cancellation
certificate is built uniformly from the exact shell; or `Theorem49ShellClaim`
itself is refuted on a shell-bearing embedding.  See `ROADMAP.md`.
-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression
open Theorem49ForcingInteriorEdgeObstructionRegression
open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
open Theorem49PositiveGeometricSourceReplacementRegression

variable {V : Type*} [DecidableEq V]

/-- Tait colorability: the edge-coloring form of the Four Color Theorem for a
single graph.  By Tait's reduction (not formalized here), the Four Color
Theorem is equivalent to `TaitColorable G` for every bridgeless cubic planar
`G`. -/
def TaitColorable (G : SimpleGraph V) : Prop :=
  ∃ C : G.EdgeColoring Color, IsTaitEdgeColoring G C

/-- The manuscript-shaped Theorem 4.9 target: the boundary-root synthesis on
every plane embedding with boundary that carries the exact closed-walk shell,
for the shell's own Tait coloring. -/
def Theorem49ShellClaim : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W} [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (shell : ClosedWalkExactShell emb),
      Theorem49BoundaryRootSynthesis emb shell.tait.coloring

/-- Uniform oracle: every shell-bearing embedding admits repaired
previous-boundary witness geometry. -/
def PreviousBoundaryGeometryOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W}
    (emb : PlaneEmbeddingWithBoundary G), Nonempty (ClosedWalkExactShell emb) →
      Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)

/-- Uniform oracle: every shell-bearing embedding admits explicit well-founded
face-peel witness data. -/
def WellFoundedPeelOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W}
    (emb : PlaneEmbeddingWithBoundary G), Nonempty (ClosedWalkExactShell emb) →
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb)

/-- Uniform oracle: every shell-bearing embedding admits generic interior-dual
boundary-root distance-peel data. -/
def InteriorDualPeelOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W}
    (emb : PlaneEmbeddingWithBoundary G), Nonempty (ClosedWalkExactShell emb) →
      Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)

/-- Uniform oracle form of the v23.5 residual/current-boundary repair lane:
every shell-bearing embedding admits the residual positive wrapper. -/
def ResidualBoundaryGeometryOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W}
    (emb : PlaneEmbeddingWithBoundary G), Nonempty (ClosedWalkExactShell emb) →
      Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb

/-- Uniform non-geometric candidate repair lane: every exact shell already
supplies the projected-generator detector certificate suggested by the finite
lab's explicit algebraic cancellation checks. -/
def AlgebraicCancellationOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W} [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (shell : ClosedWalkExactShell emb),
      BoundaryZeroProjectedGeneratorDetector emb shell.tait.coloring

/-- Weaker and more lab-faithful non-geometric candidate repair lane: every exact shell admits
some explicit coloring family inside the shell Tait coloring's edge-Kempe closure that already
detects every nonzero selected-boundary-zero chain. -/
def AlgebraicNeighborhoodCancellationOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W} [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (shell : ClosedWalkExactShell emb),
      ∃ colorings : Set (G.EdgeColoring Color),
        colorings ⊆ G.EdgeKempeClosure shell.tait.coloring ∧
          BoundaryZeroProjectedColoringGeneratorDetector emb colorings

/-- Direct kernel-check form of the same explicit-family repair lane: every exact shell admits an
explicit Kempe-neighborhood family whose concrete family-evaluation pairing map has trivial
kernel.  This matches the finite-lab certificate shape before upgrading it to the detector
surface. -/
def AlgebraicNeighborhoodPairingKernelOracle : Prop :=
  ∀ {W : Type} [DecidableEq W] {G : SimpleGraph W} [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (shell : ClosedWalkExactShell emb),
      ∃ colorings : Set (G.EdgeColoring Color),
        colorings ⊆ G.EdgeKempeClosure shell.tait.coloring ∧
          ∃ κ : Type,
            ∃ family : κ → projectedColoringGeneratorSubspace emb colorings,
              LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥

/-! ## The claim follows from any uniform oracle -/

theorem theorem49ShellClaim_of_previousBoundaryGeometryOracle
    (h : PreviousBoundaryGeometryOracle) : Theorem49ShellClaim := by
  intro W _ G _ _ emb shell
  obtain ⟨geometry⟩ := h emb ⟨shell⟩
  exact boundaryRootSynthesis_of_closedWalkExactShell_and_previousBoundaryWitnessGeometry
    shell geometry

theorem theorem49ShellClaim_of_wellFoundedPeelOracle
    (h : WellFoundedPeelOracle) : Theorem49ShellClaim := by
  intro W _ G _ _ emb shell
  obtain ⟨data⟩ := h emb ⟨shell⟩
  exact boundaryRootSynthesis_of_closedWalkExactShell_and_wellFoundedPeelWitnessData
    shell data

theorem theorem49ShellClaim_of_interiorDualPeelOracle
    (h : InteriorDualPeelOracle) : Theorem49ShellClaim := by
  intro W _ G _ _ emb shell
  obtain ⟨peel⟩ := h emb ⟨shell⟩
  exact boundaryRootSynthesis_of_closedWalkExactShell_and_interiorDualPeelData shell peel

theorem theorem49ShellClaim_of_residualBoundaryGeometryOracle
    (h : ResidualBoundaryGeometryOracle) : Theorem49ShellClaim := by
  intro W _ G _ _ emb shell
  exact
    theorem49BoundaryRootSynthesis_of_collarLayerPositiveProjectedGeometryOn
      (theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
        (h emb ⟨shell⟩))
      shell.tait.coloring shell.tait.isTait

theorem theorem49ShellClaim_of_algebraicCancellationOracle
    (h : AlgebraicCancellationOracle) : Theorem49ShellClaim := by
  intro W _ G _ _ emb shell
  exact
    boundaryRootSynthesis_of_closedWalkExactShell_and_boundaryZeroProjectedGeneratorDetector
      shell (h emb shell)

theorem algebraicCancellationOracle_of_algebraicNeighborhoodCancellationOracle
    (h : AlgebraicNeighborhoodCancellationOracle) : AlgebraicCancellationOracle := by
  intro W _ G _ _ emb shell
  rcases h emb shell with ⟨colorings, hsubset, hdet⟩
  exact BoundaryZeroProjectedGeneratorDetector.of_coloringFamily hsubset hdet

theorem algebraicNeighborhoodCancellationOracle_of_algebraicNeighborhoodPairingKernelOracle
    (h : AlgebraicNeighborhoodPairingKernelOracle) :
    AlgebraicNeighborhoodCancellationOracle := by
  intro W _ G _ _ emb shell
  rcases h emb shell with ⟨colorings, hsubset, κ, family, hker⟩
  exact ⟨colorings, hsubset,
    detector_of_ker_planarBoundaryZeroFamilyPairingMap_eq_bot family hker⟩

theorem theorem49ShellClaim_of_algebraicNeighborhoodCancellationOracle
    (h : AlgebraicNeighborhoodCancellationOracle) : Theorem49ShellClaim :=
  theorem49ShellClaim_of_algebraicCancellationOracle
    (algebraicCancellationOracle_of_algebraicNeighborhoodCancellationOracle h)

theorem theorem49ShellClaim_of_algebraicNeighborhoodPairingKernelOracle
    (h : AlgebraicNeighborhoodPairingKernelOracle) : Theorem49ShellClaim :=
  theorem49ShellClaim_of_algebraicNeighborhoodCancellationOracle
    (algebraicNeighborhoodCancellationOracle_of_algebraicNeighborhoodPairingKernelOracle h)

/-! ## All four uniform oracles are false

The benchmarks inhabit the exact shell while refuting the geometry, so no
derivation can pass uniformly from the shell to any of the three inputs.
This is the formal content of the audit: the manuscript's stated hypotheses
do not supply the geometry its Theorem 4.9 argument consumes. -/

theorem not_interiorDualPeelOracle : ¬ InteriorDualPeelOracle := by
  intro h
  exact not_forall_interiorDualPeelData_of_closedWalkExactShell_wheel
    (fun emb hshell => h emb hshell)

theorem not_wellFoundedPeelOracle : ¬ WellFoundedPeelOracle := by
  intro h
  obtain ⟨source⟩ := nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource
  obtain ⟨data, hnum, hboundary⟩ :=
    exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source
  obtain ⟨wf⟩ :=
    h sharedInteriorPairAnnulusEmbedding
      ⟨{ source := source
         oneCollar := ⟨data, hnum, hboundary⟩
         tait :=
           TaitV23Data.ofTait sharedInteriorPairTaitEdgeColoring
             sharedInteriorPairTaitEdgeColoring_isTait red blue ∅
         endpoint := hasUnblockedInteriorEndpoint_sharedInteriorPair }⟩
  exact
    sharedInteriorPair_closedWalkSource_tait_hasUnblockedInteriorEndpoint_without_witnessCoverData.2.2.2.1
      ⟨wf.toPlanarBoundaryHeightOrderedFacePeelWitnessData⟩

theorem not_previousBoundaryGeometryOracle : ¬ PreviousBoundaryGeometryOracle := by
  intro h
  obtain ⟨emb, hshell, _, _, hNotClosedWalkCollar, _⟩ :=
    exists_closedWalkExactShell_without_replacementPositiveGeometry_sharedInteriorPair
  obtain ⟨shell⟩ := hshell
  obtain ⟨geometry⟩ := h emb ⟨shell⟩
  exact hNotClosedWalkCollar
    (theorem49ClosedWalkAnnulusCollarPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySource_and_annulusPreviousBoundaryWitnessGeometry_and_hasUnblockedInteriorEndpoint
      shell.source geometry shell.endpoint)

/-- The v23.5 repair, as currently specified, is also false as a uniform
oracle: its positive wrapper is fixed-embedding equivalent to the collar-layer
surface, which the shared-interior-pair benchmark refutes while inhabiting the
shell.  Any surviving v23.5 route must therefore introduce a genuinely new
interface that bypasses this equivalence.  The new detector oracle above is
one precise formal candidate: it matches the finite lab's explicit algebraic
cancellation certificates, but it is not presently derived from the exact
shell uniformly. -/
theorem not_residualBoundaryGeometryOracle : ¬ ResidualBoundaryGeometryOracle := by
  intro h
  obtain ⟨emb, hshell, _, hNotCollar, _, _⟩ :=
    exists_closedWalkExactShell_without_replacementPositiveGeometry_sharedInteriorPair
  exact hNotCollar
    (theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn.1
      (h emb hshell))

end Mettapedia.GraphTheory.FourColor
