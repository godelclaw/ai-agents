import Mettapedia.GraphTheory.FourColor.Theorem49StrengthenedConditionAtMostOneDerivation
import Mettapedia.GraphTheory.FourColor.Theorem49DerivationImpossibilitySummary

/-!
# Next hard problem for Theorem 4.9 route

## Summary of confirmed impossibility results

This session investigated whether the previous impossibility results were based on a
misunderstanding of the boundary partition structure. After careful analysis:

**CONFIRMED:** The impossibility results in `Theorem49CyclicSourceAtMostOneDerivation`
and `Theorem49AtMostOneNonemptyCarrierImpossibility` are CORRECT.

### Key finding

The shared-interior-pair witness demonstrates that:
- sipFace0 has boundary [sip01, sip12, sip23, sip30]
- sip01, sip12: interior edges (consecutive, positions 0-1)
- sip23, sip30: selected boundary edges (consecutive, positions 2-3)

The selected edges form a contiguous arc even though the face has TWO interior edges.
This validates the impossibility: selectedBoundaryArc contiguity does NOT force at-most-one.

### Why contiguity alone doesn't work

Contiguity only requires selected edges to occupy a single interval in the face boundary
run. It does NOT require interior edges to be spread out. If all interior edges cluster
at one end, selected edges can form a contiguous arc at the other end.

## Characterization of the obstruction

The shared-interior-pair witness has a specific structure:
1. sipFace0 has exactly 4 edges
2. Interior edges are ADJACENT (both at the "start" of the cycle)
3. Selected edges are ADJACENT (both at the "end" of the cycle)
4. All selected edges belong to the SAME boundary component (outer)

## Potential strengthened conditions

To force at-most-one, we would need to rule out configurations like the shared-interior-pair.
Possible strengthening approaches:

### Option 1: Boundary mixing requirement
**Condition:** Every face must intersect BOTH outer and inner ambient boundaries.

**Analysis:** The shared-interior-pair witness has sipFace0 touching only the outer
boundary (sip23, sip30 ∈ outer; no edges in inner). Requiring both boundaries would
rule out this witness.

**Problem:** Even with both boundaries present, at-most-one is not guaranteed. We could
have [outer, inner, interior, interior] with selected {outer, inner} contiguous.

### Option 2: Interior edge separation requirement
**Condition:** Interior edges on a face cannot be adjacent in the face boundary.

**Analysis:** The shared-interior-pair has sip01, sip12 adjacent. This condition would
directly rule it out.

**Problem:** This is a very strong geometric constraint with unclear motivation. Why
should interior edges be separated?

### Option 3: Minimum face size requirement
**Condition:** Every face has at least k edges (for some k > 4).

**Analysis:** With more edges, it might be harder to keep interior edges clustered.
But even with 5+ edges, we could have [int, int, sel, sel, sel] satisfying contiguity.

**Problem:** Doesn't force at-most-one without additional structure.

### Option 4: Selected boundary density requirement
**Condition:** Selected edges must occupy > 50% of face boundary positions.

**Analysis:** With 2 interior and 2 selected (50%), this is barely satisfied. Requiring
> 50% means at least 3 selected for 4 total, but that allows at most 1 interior ✓

**Problem:** This is essentially ASSUMING at-most-one in a different form. Not a derivation.

## The real question

None of these strengthenings feel NATURAL or MOTIVATED by the four-color proof structure.
They all feel like ad-hoc patches designed specifically to rule out the shared-interior-pair.

The deeper question: **Why does the four-color theorem route ACTUALLY need at-most-one?**

Looking at the witness choice mechanism:
- For each face, we need to choose a witness from interior edge endpoints
- With multiple interior edges, the choice is ambiguous
- The "canonical" choice tries to use a deterministic rule

**Alternative approach:** Instead of forcing at-most-one, we could:
1. Develop a canonical choice rule that works even with multiple interior edges
2. Prove that different choices lead to the same Tait coloring
3. Or: show that faces with multiple interior edges don't affect the final argument

## Recommendation

Rather than continuing to search for ad-hoc strengthenings, we should:

1. **Investigate the witness choice ambiguity problem directly**
   - Can we define a canonical witness choice for faces with 2+ interior edges?
   - What properties must the choice satisfy for the route to work?

2. **Extend the forcing-edge obstruction family**
   - The forcing-edge obstructions are geometric constraints that actually arise
     from the proof structure
   - Adding more obstruction cases might naturally lead to at-most-one

3. **Accept at-most-one as an independent hypothesis**
   - Document that it's NOT derivable from cyclic source
   - Characterize graph classes where it holds naturally
   - Proceed with the route under this hypothesis

My recommendation: **Option 3** for now. The impossibility results are established and
documented. The route hypothesis structure is minimal. Further calibration or derivation
attempts without new insights would be unproductive.

Next session should either:
- Extend forcing-edge obstructions (if there are clear next cases)
- OR: Move to a different hard problem in the four-color route
- NO: Continue searching for ad-hoc strengthenings of the cyclic source

-/

namespace Mettapedia.GraphTheory.FourColor

/-!
## Status of hard problems

### Completed this session
- ✓ Confirmed impossibility: cyclic source ↛ at-most-one
- ✓ Confirmed impossibility: at-most-one ↛ nonempty carrier
- ✓ Investigated strengthened conditions (no natural candidates found)
- ✓ Documented findings and recommendations

### Remaining hard problems
1. Extend forcing-edge obstruction family (if applicable)
2. Resolve witness choice ambiguity for multiple interior edges
3. Move to next hard problem in four-color route

### NOT recommended
- Adding more calibration models (moratorium still in effect)
- Searching for ad-hoc condition strengthenings without motivation
- Attempting derivations already proven impossible
-/

end Mettapedia.GraphTheory.FourColor
