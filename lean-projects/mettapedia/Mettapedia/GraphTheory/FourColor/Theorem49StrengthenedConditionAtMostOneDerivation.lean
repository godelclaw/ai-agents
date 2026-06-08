import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

/-!
# Strengthened condition for at-most-one derivation

This file investigates whether STRENGTHENED conditions beyond bare cyclic source
can force at-most-one interior edge per face.

## Background

The impossibility result in `Theorem49CyclicSourceAtMostOneDerivation` showed that
cyclic source alone doesn't force at-most-one. But that analysis was based on a
partition that allowed "ambient boundary edges" distinct from "selected boundary edges."

## Key clarification

Looking at `PlanarBoundaryAnnulusBoundaryData`, the structure actually has:
- `outerAmbientBoundary ⊆ selectedBoundarySupport` (line 17-18)
- `innerAmbientBoundary ⊆ selectedBoundarySupport` (line 19-20)
- `selectedBoundarySupport ⊆ outerAmbientBoundary ∪ innerAmbientBoundary` (line 21-23)

This means: **ambient boundary = selected boundary**. There's no notion of
"non-selected ambient edges."

## Corrected partition

Every edge in a face boundary is EITHER:
1. Selected boundary (totalIncidenceCount = 1), OR
2. Interior (totalIncidenceCount ≥ 2)

This is a COMPLETE, DISJOINT partition.

## The derivation question

Given:
1. A face f
2. Selected boundary edges on f form ONE contiguous arc (from `selectedBoundaryArc`)
3. All selected boundary edges on f belong to the same boundary component
   (from `BoundaryComponentConstantOnFace`)

Does this force f to have at most one interior edge?

## Proof sketch

Suppose for contradiction f has two distinct interior edges e₁, e₂.
- e₁, e₂ are at positions i, j in the face boundary linear representation
- All other edges are selected boundary edges
- For selected edges to form a contiguous subsequence, they must occupy a single
  interval [start, end] in the linear representation
- But the selected edges are "all positions except i and j"
- For n total edges with interior at positions i < j, selected edges are at:
  {0, 1, ..., i-1, i+1, ..., j-1, j+1, ..., n-1}
- This is NOT a single interval (there's a gap at i and another at j)

**CRITICAL ISSUE:** Linear vs cyclic contiguity.

If the face boundary run uses a FIXED canonical starting point, the above argument works.

But if the face boundary can be rotated (different valid starting points for the same cycle),
then we need to check contiguity under rotation.

On a cycle, consider n=5 edges [e₀, e₁, e₂, e₃, e₄] with interior at positions 1 and 3:
- Selected edges: {e₀, e₂, e₄}
- Linear contiguity: {e₀, e₂, e₄} is NOT contiguous in [e₀, e₁, e₂, e₃, e₄]
- Cyclic contiguity: even with rotation, can we make {e₀, e₂, e₄} contiguous?
  - Rotation to start at e₀: [e₀, e₁, e₂, e₃, e₄] - not contiguous
  - Rotation to start at e₁: [e₁, e₂, e₃, e₄, e₀] - not contiguous
  - Rotation to start at e₂: [e₂, e₃, e₄, e₀, e₁] - not contiguous
  - Rotation to start at e₃: [e₃, e₄, e₀, e₁, e₂] - not contiguous
  - Rotation to start at e₄: [e₄, e₀, e₁, e₂, e₃] - not contiguous

In ALL rotations, there's a non-selected edge between any two selected edges!

## Key observation

Even with cyclic contiguity (allowing arbitrary rotations), if we have TWO interior edges,
the selected edges cannot form a single contiguous arc.

Proof: With interior edges at positions i and j (i < j in some rotation), the
selected edges are partitioned into intervals:
- Interval 1: positions [0, i-1]
- Gap at position i (interior)
- Interval 2: positions [i+1, j-1]
- Gap at position j (interior)
- Interval 3: positions [j+1, n-1] (wraps to position 0 in cyclic)

For selected edges to be contiguous, we need all three intervals to merge into one.
But with TWO gaps, we have AT LEAST two separate intervals, not one.

EXCEPTION: If one of the intervals is EMPTY. For example:
- If i = 0 and j = 2, then interval 1 is empty, and intervals 2 and 3 might merge.
- Selected edges at positions {1, 3, 4, ..., n-1}
- Is this contiguous? Only if j+1 = 1, i.e., j = 0 in the cyclic order
- But we said i = 0 and j = 2, so they're not adjacent

Let me think more carefully. With n=5 and interior at i=1, j=3:
- Selected at positions {0, 2, 4}
- Can these be contiguous in any rotation?
- Contiguous means they form an interval [start, end] with NO gaps
- {0, 2, 4}: gap at 1, gap at 3
- In rotation [2, 3, 4, 0, 1]: selected at {2, 4, 0} = positions {0, 2, 3}
  Wait, I need to relabel. After rotation, positions are [0, 1, 2, 3, 4] mapping to edges [e₂, e₃, e₄, e₀, e₁]
  Selected edges {e₀, e₂, e₄} are at positions {3, 0, 2} in this rotation
  = {0, 2, 3} after sorting
  Gap at position 1 (e₃ is interior)
  So not contiguous

Hmm, let me think about when {0, 2, 4} can be contiguous in a cyclic 5-element list.
- As an interval [start, end], we need all positions in [start, end] mod 5 to be selected
- {0, 2, 4} has gaps at 1 and 3
- No interval can cover {0, 2, 4} without also covering 1 or 3

So even with cyclic contiguity, two interior edges force selected edges to be non-contiguous!

## Conclusion

The combination of:
1. Selected boundary arc contiguity (from `selectedBoundaryArc` in the source)
2. Boundary component constancy on each face (from `BoundaryComponentConstantOnFace`)
3. The partition property (every edge is selected OR interior)

DOES force at-most-one interior edge per face, even with cyclic contiguity!

The previous impossibility result in `Theorem49CyclicSourceAtMostOneDerivation` was
based on a misunderstanding of the partition - it assumed there could be "ambient
non-selected edges" which don't exist in the actual structure.

## Next step

Formalize this derivation properly.
-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

variable {V : Type*} [DecidableEq V]

/-!
### Attempt 1: Direct derivation from selected boundary arc contiguity

The plan: show that if selected edges form a contiguous arc and there are two
interior edges, we get a contradiction.

**Blocker:** Need to formalize what "contiguous arc on a cycle" means when the
cycle can be rotated.

The `SelectedBoundaryArcOnFace` uses `<:+:` (list infix) on a specific linear
representation. But for a cyclic face boundary, is this representation canonical?
-/

/-!
### Investigation: How is the face boundary run chosen?

Looking at `PlanarBoundaryFaceBoundaryRunGeometry`, it provides a `faceBoundaryRun`
for each face. The question is: for a cyclic face boundary, does this run have a
canonical starting point?

If YES: the linear contiguity argument works directly.
If NO: we need to extend the argument to cyclic contiguity.

Let me check whether the closed walk structure provides a canonical orientation...
-/

/-!
### Key insight: Closed walks provide canonical orientation

The `PlanarBoundaryClosedWalkEmbeddingData` requires that each face has a CLOSED WALK
starting from a designated vertex. This gives a canonical orientation and starting point
for the face boundary.

With a canonical starting point, the linear contiguity check is well-defined and
unambiguous. The selected boundary arc is contiguous relative to THIS SPECIFIC
linear representation.

Therefore, the linear argument applies directly, without needing to consider rotations!
-/

/-!
### Formalization strategy

To prove: If a face f has two distinct interior edges, then the selected boundary
edges on f cannot form a contiguous subsequence of the canonical face boundary run.

This will contradict the `selectedBoundaryArc` property, establishing impossibility.

The proof needs:
1. The partition: every edge is selected XOR interior
2. The face boundary run as a list
3. The positions of the two interior edges in this list
4. Show that selected edges (all other positions) don't form a contiguous interval

**Challenge:** Formalizing "two gaps in a list means the complement isn't a contiguous interval"

Let me look for existing lemmas about list subseqs and gaps...
-/

/-!
### Alternative route: Count-based argument

Instead of reasoning about positions and gaps, use a counting argument:

Given:
- Face boundary has n edges total
- k edges are interior (we want to show k ≤ 1)
- n - k edges are selected boundary
- Selected edges form ONE contiguous arc

Claim: If k ≥ 2, the selected edges cannot form a single contiguous arc.

Proof idea: A contiguous arc of length m in a cyclic list of length n can "skip" at most
one contiguous block of non-arc elements. With k ≥ 2 interior edges, if they're not
adjacent, we have at least two separate blocks of non-arc elements, contradiction.

**Special case:** What if all k interior edges are CONSECUTIVE?
- Then selected edges form the complement, which IS a single arc!
- But wait, we also need boundary component constancy...

Ah! Here's the key: if a face has two interior edges e₁, e₂, and they're both interior,
then they have totalIncidenceCount ≥ 2, meaning they each appear on at least one OTHER face.

Hmm, but that's about the global structure, not the local face structure.

Let me reconsider...
-/

/-!
### Realization: The previous impossibility result may be CORRECT

Going back to the `Theorem49CyclicSourceAtMostOneDerivation` file, it says:

"The derivation requires reasoning about CYCLIC ORDERING of the face boundary.
The face boundary is a cycle, but the contiguous arc property is stated on a LIST
(which has a linear order, not cyclic)."

And then it gives a counterexample:
```
Face boundary (linear representation): [e₁, e₂, e₃, e₄, e₅]
- e₁: selected boundary edge
- e₂: interior edge
- e₃: ambient boundary edge (outer or inner)
- e₄: interior edge
- e₅: ambient boundary edge (outer or inner)
```

But I've now established that e₃ and e₅ CANNOT be "ambient but not selected" - they
must be EITHER selected OR interior!

So if they're ambient, they're selected. Then the face has selected edges {e₁, e₃, e₅},
which is NOT contiguous in the linear representation [e₁, e₂, e₃, e₄, e₅].

This VIOLATES the selectedBoundaryArc contiguity property!

So the counterexample in that file is INVALID.

## Verdict: The previous impossibility result is CORRECT

Checking the shared-interior-pair witness more carefully:
- sipFace0 boundary: [sip01, sip12, sip23, sip30]
- sip01, sip12: interior edges
- sip23, sip30: selected boundary edges

The selected edges {sip23, sip30} occupy positions 2 and 3, which ARE consecutive.
So they form a contiguous subsequence [sip23, sip30] of the full boundary.

This satisfies the `selectedBoundaryArc` contiguity property, even though the face
has TWO interior edges!

The key insight: Contiguity only requires selected edges to be consecutive. It does NOT
require interior edges to be spread out. If all interior edges are bunched together
at one end of the face boundary, the selected edges can still form a contiguous arc
at the other end.

## Conclusion

The selectedBoundaryArc contiguity, even combined with boundary component constancy,
does NOT force at-most-one interior edge per face.

The previous impossibility result in `Theorem49CyclicSourceAtMostOneDerivation` is
CORRECT, and the shared-interior-pair witness validates it.

## Next direction

Since cyclic source alone cannot derive at-most-one, we need to investigate what
ADDITIONAL conditions would suffice.

Possible strengthened conditions:
1. Require selected boundary edges to be WELL-DISTRIBUTED (not just contiguous)
   - E.g., selected edges must occupy at least half the face boundary
   - Or: interior edges must be non-adjacent
2. Add geometric constraints on the embedding structure
   - Triangulated faces
   - Bounded degree
3. Add topological constraints
   - Genus bounds
   - Separating properties

For now, the derivation impossibility is established and documented. The theorems
below record the route-facing strengthened-source version directly: even the
same-embedding boundary reachability field, successor-cycle geometry, selected
boundary arcs, and boundary-component constancy do not force at-most-one.
-/

/-- The shared-interior-pair model carries the strengthened route-facing source fields
explicitly: boundary reachability, successor-cycle facial geometry, and selected-boundary arcs.
Nevertheless it fails the face-local at-most-one-interior-edge condition. -/
theorem
    exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_atMostOneInteriorEdgePerFace_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ¬ ∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1 := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      not_sharedInteriorPair_atMostOneInteriorEdgePerFace⟩

/-- Boundary reachability plus successor-cycle facial geometry plus selected-boundary arcs still
does not imply the face-local at-most-one-interior-edge condition. -/
theorem
    not_forall_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_implies_atMostOneInteriorEdgePerFace_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1 := by
  intro h
  exact
    not_sharedInteriorPair_atMostOneInteriorEdgePerFace
      (h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace)

/-- Even adding the boundary-component constancy normally derived from the honest source fields
does not make selected-boundary arc data imply at-most-one. -/
theorem
    not_forall_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryComponentConstant_implies_atMostOneInteriorEdgePerFace_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
          (∀ f : AmbientFace emb.faces, boundaryData.BoundaryComponentConstantOnFace f) →
            ∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1 := by
  intro h
  exact
    not_sharedInteriorPair_atMostOneInteriorEdgePerFace
      (h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        (fun f =>
          sharedInteriorPairDartSuccessorClosedWalkAnnulusBoundarySource.boundaryComponentConstantOnFace
            (f := f)))

end Mettapedia.GraphTheory.FourColor
