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
| `Goal.lean` | The target (`Theorem49ShellClaim`), its reduction to four geometric oracles, and proofs that **all four uniform oracles are false** — including the v23.5 residual/current-boundary lane, whose positive wrapper is fixed-embedding equivalent to the refuted collar-layer surface |
| `Shells.lean` | Bundled hypothesis packages (`ClosedWalkExactShell`, `SuccessorCycleExactShell`, …) replacing the historical 8–10-hypothesis telescopes |
| `Frontier.lean` | The maximal positive and negative results, stated over the bundles as thin wrappers |

## Current status (one paragraph)

The positive lane is complete from geometry upward: repaired previous-boundary
witness geometry, explicit well-founded peel-witness data, or generic
interior-dual distance-peel data on the shell's embedding each yield full
`Theorem49BoundaryRootSynthesis` (`Frontier.lean`, wrapping the route files).
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
"algebraic cancellation certificate" obligation — a genuinely new interface —
remains live.  Structurally, any shell with an
unblocked endpoint forces two distinct interior edges on some face boundary
(`Frontier.lean`), which is what kills the facewise-at-most-one,
canonical-choice, and source-preserving one-collar repair lanes.

## The open problem

Exactly one question is live, as a dichotomy:

1. **Repair**: find same-embedding geometric hypotheses that (a) are
   natural for the manuscript's induction, (b) are *not* satisfied by the
   wheel/shared-interior-pair benchmarks, and (c) construct one of the four
   oracle inputs.  Everything at or below the exact shells is proven
   insufficient; candidate hypotheses must be checked against the benchmarks
   *first* (5-minute check) before building route surface (multi-day work).
2. **Refute**: decide `Theorem49BoundaryRootSynthesis` on a shell-bearing
   benchmark embedding (the wheel is the simplest).  If it is *false* there,
   `Theorem49ShellClaim` is refuted outright and the manuscript's Theorem 4.9
   is false as stated — the audit terminates with a concrete counterexample.
   Notably, this direct check appears undecided in the current tree: the
   ledger proves the synthesis on a *degenerate* wheel embedding
   (`wheelWithInnerTriangleDegenerateEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring`)
   but neither proves nor refutes it on the shell-bearing
   `wheelWithInnerTriangleEmbedding`; all current refutations there are about
   intermediate geometry layers, not the synthesis endpoint itself.

Direction 2 is the cheaper experiment and should be tried before any further
route surface is added.

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
- **`Legacy/`** (19 files, ~39k lines): the historical obstruction ledger.
  Fully verified, frozen.  Its maximal results are re-exported by
  `Frontier.lean`; weaker shells refuted there are subsumed a fortiori.  Do
  not add to it; do not build on it except through `Frontier`.

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
