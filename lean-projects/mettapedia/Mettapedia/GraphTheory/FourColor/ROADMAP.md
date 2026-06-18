# FourColor: goal, status, and how to approach it

*Last restructured: 2026-06-10.  This file replaces the 3,577-line
`Theorem49NextHardProblemSummary.lean` prose (now in `Legacy/`) as the
entry point.*

## The goal

By Tait's classical reduction, the Four Color Theorem is equivalent to: every
bridgeless cubic planar graph has a proper 3-edge-coloring
(`IsTaitEdgeColoring`).  Goertzel's v23 manuscript attacks this via an
inductive boundary argument whose load-bearing step is **Theorem 4.9**: an
F₂-algebraic synthesis (`Theorem49BoundaryRootSynthesis`) saying the
boundary-zero Kirchhoff subspace is spanned by projected Kempe-closure
generators on a plane embedding with boundary.  This development is the formal
audit and (attempted) formalization of that step.

Read these three files first — they are the whole live surface:

| File | Contents |
|---|---|
| `Goal.lean` | The target (`Theorem49ShellClaim`), its reduction to four geometric oracles plus a fifth non-geometric algebraic cancellation oracle, and proofs that **all four geometric uniform oracles are false** — including the v23.5 residual/current-boundary lane, whose positive wrapper is fixed-embedding equivalent to the refuted collar-layer surface |
| `Shells.lean` | Bundled hypothesis packages (`ClosedWalkExactShell`, `SuccessorCycleExactShell`, `ClosedWalkCancellationShell`, …) replacing the historical 8–10-hypothesis telescopes |
| `Frontier.lean` | The maximal positive and negative results, stated over the bundles as thin wrappers, including detector-based cancellation sufficiency |

## Current status (one paragraph)

The positive lane is complete from geometry upward: repaired previous-boundary
witness geometry, explicit well-founded peel-witness data, or generic
interior-dual distance-peel data on the shell's embedding each yield full
`Theorem49BoundaryRootSynthesis` (`Frontier.lean`, wrapping the route files).
The same file now also exposes a non-geometric positive lane: an exact shell
plus the projected-generator detector certificate
(`BoundaryZeroProjectedGeneratorDetector`) also yields full synthesis, and
`Goal.lean` now packages both the old whole-closure uniform hypothesis
`AlgebraicCancellationOracle` and the weaker, lab-faithful
`AlgebraicNeighborhoodCancellationOracle`, which only asks for some explicit
detecting coloring family inside the shell Tait coloring's edge-Kempe closure.
The live shell/frontier surface now also carries the direct kernel-check form
of that same obligation: `Shells.lean` bundles exact shells together with an
explicit family whose concrete pairing map has trivial kernel, `Frontier.lean`
proves that this already yields full theorem-4.9 synthesis, and `Goal.lean`
packages the corresponding uniform hypothesis as
`AlgebraicNeighborhoodPairingKernelOracle`.
The negative lane is complete from the shells downward: the
wheel-with-inner-triangle and shared-interior-pair benchmarks inhabit the full
endpoint-bearing exact one-collar/v23 shells while refuting every named
geometric layer, so no uniform derivation from the manuscript's stated
hypotheses to the geometry its argument consumes can exist
(`Goal.lean: not_interiorDualPeelOracle, not_wellFoundedPeelOracle,
not_previousBoundaryGeometryOracle, not_residualBoundaryGeometryOracle`).
The last of these is the formal verdict on the v23.5 revision memo's repair
proposal: the residual/current-boundary lane as currently specified is
conservative over the refuted collar-layer surface, so only its unformalized
"algebraic cancellation certificate" obligation remained live in prose.  The
new live-surface files now formalize that obligation directly as the shell-wise
detector oracles above: it is no longer just roadmap prose, but unlike the
geometric oracles it is not presently refuted by the current shell-bearing
benchmarks.  Moreover, the new file
`Mettapedia/GraphTheory/FourColor/Theorem49ColoringGeneratorFamilyRoute.lean`
proves that a detector on any explicit coloring family inside the base
edge-Kempe closure already upgrades to the full theorem-4.9 synthesis
endpoint.  So the live non-geometric lane no longer has to be phrased as a
whole-closure detector; it can match the finite lab's smaller explicit
neighborhood certificates directly.  A new kernel-checked theorem now sharpens
the comparison:
`Theorem49DetectorStrength.lean` proves that on every shell-bearing embedding
the theorem-4.9 target `W₀(H)` is a proper subspace of the full
selected-boundary-zero chain space.  So the detector/cancellation oracle is
strictly stronger than the manuscript target on the current shell surface; it
is not merely a restatement of theorem 4.9 in different words.  Structurally, any shell with an
unblocked endpoint forces two distinct interior edges on some face boundary
(`Frontier.lean`), which is what kills the facewise-at-most-one,
canonical-choice, and source-preserving one-collar repair lanes.  Update
2026-06-11: the new finite lab under `scripts/4cp_lab/` directly decides the
current endpoint on the small explicit benchmarks.  It reproduces the positive
degenerate wheel and diamond-with-triangle cases, and finds
`Theorem49BoundaryRootSynthesis` true on the shell-bearing
`wheelWithInnerTriangleEmbedding` and `sharedInteriorPairAnnulusEmbedding` for
their explicit benchmark colorings; on the same embeddings it is also true for
all 36 wheel Tait colorings and all 72 shared-interior-pair Tait colorings
enumerated by the lab.  A follow-up detector experiment now localizes the
annihilator burden further: for the wheel benchmark, the explicit coloring
alone already kills every selected-boundary-zero annihilator, while for the
shared-interior-pair benchmark the explicit coloring plus its six one-step
Kempe neighbors already suffice.  The wheel explicit-coloring case is now
kernel-checked in Lean by
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49WheelEndpointRegression.lean`,
and `Mettapedia/GraphTheory/FourColor/Legacy/Theorem49WheelFullSweepRegression.lean`
now upgrades that explicit endpoint to all 36 wheel Tait colorings.  The
shared-interior-pair benchmark now has kernel-checked representatives for both
of the 36-color Kempe-closure classes found by the lab, via
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49SharedInteriorPairEndpointRegression.lean`
and
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49SharedInteriorPairSecondClosureEndpointRegression.lean`.
The new file
`Mettapedia/GraphTheory/FourColor/Theorem49SynthesisClosureInvariance.lean`
then proves that the full theorem-4.9 synthesis package depends only on the
underlying `EdgeKempeClosure` class of the base coloring, and can be
transported along mutual edge-Kempe reachability.  So the remaining Lean gap
on the current pathologies is no longer the wheel sweep, no longer a missing
shared representative, and no longer the shared class-membership /
classification step either: the new file
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49SharedInteriorPairFullSweepRegression.lean`
now classifies every Tait coloring of the shell-bearing shared benchmark into
two parametric Kempe-closure families, proves four generic closure generators
per family, reduces each family to its explicit kernel-checked representative,
and upgrades theorem 4.9 to all 72 shared Tait colorings.  So the current
explicit shell-bearing benchmarks no longer leave a Lean gap at the level of
their full finite Tait sweeps; the remaining open burden on this path is
either a wider shell-bearing search or a new general computable F₂ layer that
scales beyond these two benchmarks.  Update later on 2026-06-11: the new file
`Mettapedia/GraphTheory/FourColor/Theorem49BoundaryProjectionDetector.lean`
shows that the selected-boundary projected-generator detector property is also
an edge-Kempe-closure invariant, and the wheel/shared full-sweep regression
files now upgrade not only `Theorem49BoundaryRootSynthesis` but also that
detector property to all 36 wheel and all 72 shared Tait colorings.  So the
current finite benchmarks are now closed in Lean at the detector layer as
well, not only at the final theorem-4.9 synthesis package.  Update later still
on 2026-06-11: the exact wheel radius-0 detector certificate exposed by the
finite lab is now kernel-checked directly in
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49WheelRadiusZeroDetectorRegression.lean`,
showing that the explicit wheel coloring alone already detects every nonzero
selected-boundary-zero chain.  The exact shared radius-1 detector certificate
is now kernel-checked directly in
`Mettapedia/GraphTheory/FourColor/Legacy/Theorem49SharedInteriorPairRadiusOneDetectorRegression.lean`.
So the finite lab's two minimal explicit detector certificates are both now
Lean-native.  Moreover, Lean sharpens the lab's seven-color shared radius-1
neighborhood: for the shared explicit benchmark coloring, the detector already
follows from a two-color witness subfamily consisting only of the base coloring
and one inner red/blue Kempe neighbor.

## The open problem

Exactly one cluster of questions is live, now best stated as a trichotomy:

1. **Repair**: find same-embedding geometric hypotheses that (a) are
   natural for the manuscript's induction, (b) are *not* satisfied by the
   wheel/shared-interior-pair benchmarks, and (c) construct one of the four
   oracle inputs.  Everything at or below the exact shells is proven
   insufficient; candidate hypotheses must be checked against the benchmarks
   *first* (5-minute check) before building route surface (multi-day work).
2. **Non-geometric repair**: derive the new shell-wise detector obligation
   `AlgebraicNeighborhoodCancellationOracle` uniformly from the exact shell,
   or at least derive the stronger whole-closure
   `AlgebraicCancellationOracle`.  This is the formalized version of the
   memo's algebraic cancellation certificate: it is strong enough to imply
   `Theorem49ShellClaim`, it now matches the finite lab's explicit
   certificates at the right granularity, and the direct kernel-check shell
   form `AlgebraicNeighborhoodPairingKernelOracle` now packages those
   certificates before any upgrade to the detector surface.  The current wheel/shared
   benchmark families no longer refute it.
3. **Refute**: find a shell-bearing embedding where
   `Theorem49BoundaryRootSynthesis` itself fails.  The cheapest current
   candidates have now been checked computationally: the finite lab in
`scripts/4cp_lab/exp01_wheel_endpoint.py` finds the synthesis **true** on
the shell-bearing wheel and shared-interior-pair benchmarks, both for the
explicit benchmark colorings and for every Tait coloring the lab enumerates
there.  The companion detector experiment
`scripts/4cp_lab/exp02_kempe_detector.py` shows the remaining explicit
annihilator checks are tiny: radius `0` for the wheel and radius `1` for
the shared-interior-pair case.  Both exact certificates are now
kernel-checked directly in Lean: the wheel singleton radius-0 certificate, and
the shared radius-1 certificate, which even compresses there to a two-color
witness subfamily.  So the direct-counterexample lane survives only through a
different shell-bearing benchmark, or through a future Lean-computable F₂
elimination/search layer that scales beyond the wheel and shared-interior-pair
benchmarks already discharged in Lean.

## File organization

- **`Goal.lean`, `Shells.lean`, `Frontier.lean`** — the live surface (above).
- **Core theory** (reusable, Mathlib-style): `ColorAlgebra`, `FaceIncidence`,
  `PlanarFaceIncidence`, `Orthogonality`, `BoundaryVanishing`,
  `Theorem49LinearAlgebra`, the `PlanarBoundary*` family (embeddings,
  sources, annulus construction, peeling), `Theorem49KempeGeneratorSpan`,
  `Theorem49SpanningGap`.
- **Route files** (`Theorem49*Route`, `Theorem49Synthesis`,
  `Theorem49PositiveGeometricSource*`, …): the positive lane.  Heavily
  duplicated between closed-walk and successor-cycle presentations; new
  statements should go through `Shells.lean` bundles instead of extending
  these.
- **Load-bearing benchmark/obstruction files kept in the main tree** (they
  are imported by route files): `Theorem49AtMostOneNonemptyCarrierImpossibility`,
  `Theorem49ForcingInteriorEdgeObstruction`,
  `Theorem49InteriorVerticesEndpointObstruction`,
  `Theorem49PositiveGeometricSourceImpossibility`, and the four
  `Theorem49PlanarBoundaryAnnulus*Regression` keepers (these define the
  shared-interior-pair benchmark).
- **`Legacy/`**: the historical obstruction ledger plus the concrete explicit
  endpoint regression certificates.  Fully verified.  Its maximal results are
  re-exported by `Frontier.lean`; weaker shells refuted there are subsumed a
  fortiori.  Do not add new shell-obstruction wrappers there; do not build on
  it except through `Frontier`.

## Conventions going forward

- State new theorems over the `Shells.lean` bundles.  If a hypothesis package
  recurs three times, bundle it.
- No new 100+-character theorem names; the shell vocabulary exists so names
  can be short.
- A failed universal converse is one application of
  `not_forall_target_of_exists_shell_witness` to an explicit witness — do not
  write bespoke 60-line converse theorems.
- New benchmark counterexamples get their own file with the benchmark's facts
  proved once; obstruction theorems combine benchmark facts with shell
  definitions.
- Keep the tree sorry-free and axiom-free (it currently is).

## Build targets

- Live surface: `lake build Mettapedia.GraphTheory.FourColor.Goal`
  (pulls in `Shells`, `Frontier`, and the route files they wrap).
- Everything incl. ledger: `lake build Mettapedia.GraphTheory.FourColorRegression`.
- Dependency audit: `python3 ../../../scripts/lean_deps.py <path>`.
