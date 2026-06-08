import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

/-!
# Failed derivation: cyclic source does not force at-most-one interior edge

This file records the failed derivation from cyclic boundary-order geometry and
selected-boundary arc contiguity to at most one interior edge per face.

The key geometric insight: if a face had two distinct interior edges, and if non-interior
edges are partitioned into selected-boundary edges and ambient-boundary edges, then
the selected-boundary edges would be forced into multiple disjoint arcs (one between
each pair of interior edges), violating the contiguity condition.

## Current status

The shared-interior-pair witness below shows that the route is impossible:
honest closed-walk annulus source data can coexist with a face carrying two
interior boundary edges.
-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

variable {V : Type*} [DecidableEq V]

/-!
### Geometric setup

We have:
1. A cyclic boundary order (from closed walks)
2. Selected boundary edges form ONE contiguous arc on each face
3. An annulus boundary split (outer and inner ambient boundaries)

Question: Does this force at-most-one interior edge per face?

### Key lemma needed

If a face boundary contains two distinct interior edges, and every non-interior edge
is either a selected-boundary edge or an ambient-boundary edge, then the selected
boundary edges cannot form a single contiguous arc on the cyclic boundary.

The proof idea:
- Interior edges are disjoint from selected boundary edges (by definition)
- If we have two interior edges e₁ and e₂ at positions i and j in the cyclic order
- The selected edges must "skip" these positions
- If selected edges form ONE contiguous arc, they occupy a single interval
- But with two interior edges as "obstacles", selected edges would need to be in
  multiple intervals, contradicting contiguity
-/

/-- A face boundary run is partitioned into three disjoint types: selected boundary edges,
ambient boundary edges (outer or inner), and interior edges. -/
def FaceBoundaryPartitioned {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (f : AmbientFace emb.faces) : Prop :=
  ∀ e ∈ emb.faceBoundary f.1,
    (e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∨
    (e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary) ∨
    (e ∈ interiorEdgeSupport emb.faceBoundary emb.faces)

/-!
### Failed derivation target

If:
1. The face boundary is partitioned as above
2. Selected boundary edges form one contiguous arc
3. The face boundary has a cyclic order

Then one might hope to prove that the face has at most one interior edge.
The concrete shared-interior-pair witness below refutes this hope on the
closed-walk source surface itself.
-/

/-!
### Obstacle identified

The derivation requires reasoning about CYCLIC ORDERING of the face boundary.
The face boundary is a cycle, but the contiguous arc property is stated on a LIST
(which has a linear order, not cyclic).

The conversion from cyclic order to linear order involves choosing a "starting point"
on the cycle. Different starting points give different linear representations.

For a contiguous arc to be well-defined on a cycle, we need to know:
- Is there a canonical way to represent the cycle as a list?
- How does the contiguity property behave under cyclic rotation?

-/

/-!
### Second obstacle: multiple arc representation

Wait - I realize the issue. The `SelectedBoundaryArcOnFace` says:

```
∃ selectedRun : List G.edgeSet,
  selectedRun <:+: (geom.faceBoundaryRun f).run ∧ ...
```

The `<:+:` is the LIST INFIX relation (contiguous subsequence). But on a CYCLE,
contiguity is ambiguous without a fixed starting point.

However, if the `faceBoundaryRun f` already gives a FIXED ordered representation
of the face boundary (with a chosen starting point), then contiguity is well-defined
relative to that representation.

The question becomes: given that representation, can we have two interior edges
and still maintain contiguity of selected edges?

Let's think about this with a concrete example:
- Face boundary (as a list): [e₁, e₂, e₃, e₄, e₅]
- Suppose e₂ and e₄ are interior edges
- Suppose e₁, e₃, e₅ are non-interior

For the selected edges to form a contiguous subsequence:
- They could be [e₁], [e₃], [e₅], [e₁, e₃], [e₃, e₅], or [e₁, e₃, e₅]
- But [e₁, e₃, e₅] is NOT a contiguous subsequence of [e₁, e₂, e₃, e₄, e₅]!
- [e₁] is contiguous (positions 0-0)
- [e₁, e₃] is NOT contiguous (positions 0 and 2, with position 1 skipped)

So if e₁, e₃, e₅ are ALL selected edges, they DON'T form a contiguous block!

But wait - the face boundary partition says every non-interior edge is EITHER
selected OR ambient. It doesn't say ALL non-interior edges are selected!

So we could have:
- e₁: selected
- e₂: interior
- e₃: ambient (not selected)
- e₄: interior
- e₅: selected

In this case, selected edges are {e₁, e₅}, which is NOT contiguous in the linear
representation [e₁, e₂, e₃, e₄, e₅].

But in the CYCLIC representation, {e₁, e₅} could be contiguous if we think of
e₅ as being adjacent to e₁!

This is the CYCLIC CONTIGUITY issue. On a cycle, {e₁, e₅} can form a contiguous
arc if they're adjacent in the cyclic order.

### Real question

Is the `SelectedBoundaryArcOnFace` property defined relative to:
(a) A fixed linear representation (with a chosen starting point), OR
(b) The cyclic order (where contiguity wraps around)?

Looking at the definition again, it uses `selectedRun <:+: (geom.faceBoundaryRun f).run`,
where `run` is a LIST. So it seems to be (a) - a fixed linear representation.

But for a CYCLIC face boundary, the choice of starting point matters!

Let me investigate whether the FaceBoundaryRun structure addresses this...
-/

/-!
### NEGATIVE RESULT: Cyclic source does NOT force at-most-one

After analysis, I conclude that the cyclic source structure alone does NOT force
at-most-one interior edge per face. Here's a counterexample construction:

Face boundary (linear representation): [e₁, e₂, e₃, e₄, e₅]
- e₁: selected boundary edge
- e₂: interior edge
- e₃: ambient boundary edge (outer or inner)
- e₄: interior edge
- e₅: ambient boundary edge (outer or inner)

This satisfies:
1. Selected edges {e₁} form a contiguous subsequence ✓
2. Face has TWO interior edges {e₂, e₄} ✗ (violates at-most-one)
3. Non-interior edges partition into selected and ambient ✓

The key insight: the face boundary partition allows non-interior edges to be
EITHER selected OR ambient. So even with two interior edges "blocking" positions,
we can make the selected edges contiguous by putting all selected edges in one
contiguous block and making the other non-interior edges ambient.

### Why the current route works anyway

The current theorem-4.9 route ASSUMES at-most-one as an input hypothesis
(`h_at_most_one_interior`). It does not derive it from the cyclic source.

This means at-most-one is an ADDITIONAL geometric condition beyond the cyclic
source structure. It's a sufficient condition for witness choice, but not a
necessary consequence of the cyclic geometry.

### Implications for the derivation agenda

The verdict asked me to either:
1. Derive at-most-one from cyclic source geometry, OR
2. Prove route impossibility

I have now established (2): it is IMPOSSIBLE to derive at-most-one from the
cyclic source fields alone. The counterexample above shows a valid cyclic
source configuration with two interior edges per face.

### What about the nonempty-carrier problem?

The other hard theorem was: prove at-most-one plus specified conditions
guarantees nonempty `selectedBoundaryInteriorEdgeEndpointVertices`.

But the chained-diamonds regression shows that at-most-one does NOT guarantee
nonempty carriers! That graph satisfies at-most-one but has empty carrier.

So this suggests route impossibility for that direction as well.

### Conclusion: Route impossibility established

Both attempted derivation routes appear to be IMPOSSIBLE:

1. Cyclic source ↛ at-most-one
   - Counterexample: face with two interior edges, selected edges in one block

2. At-most-one ↛ nonempty carrier
   - Counterexample: chained-diamonds (at-most-one holds, carrier empty)

The current route correctly treats at-most-one as an INDEPENDENT sufficient
condition, not a derivable consequence. And it correctly treats nonempty carrier
as an ADDITIONAL hypothesis for non-vacuous synthesis.

### Next steps

Document this impossibility result and investigate whether there are WEAKER
conditions we can derive from the cyclic source that still give useful
geometric information.
-/

theorem route_impossibility_at_most_one_not_derivable_from_cyclic_source :
    ∃ (G : SimpleGraph (Fin 8)) (emb : PlaneEmbeddingWithBoundary G),
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        ¬ ∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1 := by
  exact
    ⟨sharedInteriorPairAnnulusGraph,
      sharedInteriorPairAnnulusEmbedding,
      nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_sharedInteriorPair_atMostOneInteriorEdgePerFace⟩

/-- Closed-walk annulus source data alone cannot imply the face-local at-most-one-interior-edge
premise. The shared-interior-pair annulus source satisfies the source package but has two
interior edges on `sipFace0`. -/
theorem not_forall_closedWalkSource_implies_atMostOneInteriorEdgePerFace :
    ¬ ∀ (G : SimpleGraph (Fin 8)) (emb : PlaneEmbeddingWithBoundary G),
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
        ∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1 := by
  intro h
  exact
    not_sharedInteriorPair_atMostOneInteriorEdgePerFace
      (h sharedInteriorPairAnnulusGraph sharedInteriorPairAnnulusEmbedding
        nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource)

end Mettapedia.GraphTheory.FourColor
