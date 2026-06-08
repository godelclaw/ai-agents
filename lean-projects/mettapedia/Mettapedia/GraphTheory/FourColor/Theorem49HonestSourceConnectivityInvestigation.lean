import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusWitnessRegression
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestGeometryRegression
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource

/-!
# Investigation: Honest sources force connectivity

This file documents the investigation into whether honest closed-walk sources force
previous-boundary witness geometry, as outlined in `Theorem49NextHardProblemSummary.lean`.

## Main finding

The `counterCollarGeometry` obstruction (which shows basic collar geometry does NOT force
previous-boundary witness) **cannot admit a honest closed-walk source** because its underlying
graph `counterGraph` is disconnected.

### Graph structure of counterCollarGeometry

The `counterGraph` is defined as:
```lean
def counterGraph : SimpleGraph (Fin 16) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(2, 3), s(4, 5), s(6, 7), s(8, 9), s(10, 11), s(12, 13), s(14, 15)} :
      Set (Sym2 (Fin 16)))
```

This graph consists of 8 **disjoint edges** with no shared vertices. It is fundamentally
disconnected - vertices from different edges are in separate connected components.

### Why this prevents facial closed walks

Face `f0` in `counterEmbedding` has boundary `{eo, ep}` where:
- `eo = s(0, 1)` (connects vertices 0 and 1)
- `ep = s(2, 3)` (connects vertices 2 and 3)

For a `FaceBoundaryClosedWalk` to exist on this face, there must be a closed walk that traverses
both edges `eo` and `ep`. But:
1. A walk is a sequence of adjacent vertices in the graph
2. To traverse both edges, the walk must form a path from {0,1} to {2,3}
3. But vertices 0,1 are only connected to each other (via `eo`)
4. And vertices 2,3 are only connected to each other (via `ep`)
5. There is **no path** between these disjoint components

Therefore, no closed walk can exist on face `f0`, which means `counterEmbedding` cannot admit
`PlanarBoundaryClosedWalkEmbeddingData`, and hence cannot admit
`PlanarBoundaryClosedWalkAnnulusBoundarySource`.

## Implications

This result is significant because:

1. **The obstruction to deriving previous-boundary witness from basic collar geometry is ruled out
   by honest sources.**

2. **This suggests honest sources might actually FORCE previous-boundary witness geometry.**

3. **The mechanism is connectivity:** Honest sources require facial closed walks, which require
   the graph to be sufficiently connected. Disconnected graphs with face boundaries spanning
   multiple components cannot admit honest sources.

## Next steps: Deriving previous-boundary witness from honest sources

The investigation strategy now becomes:

1. **Characterize the connectivity forced by honest sources**
   - What graph connectivity properties must hold for a graph to admit
     `PlanarBoundaryClosedWalkEmbeddingData`?
   - For each face, the boundary edges must form a connected subgraph

2. **Prove connectivity + collar geometry ⟹ previous-boundary witness**
   - Show that if faces have connected boundaries AND collar geometry holds,
     then witness edges must lie on previous boundaries
   - The connectivity prevents the pathological "witness on later boundary" scenario

3. **Combine into the desired theorem:**
   ```lean
   theorem honest_source_forces_previous_boundary_witness
       {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
       (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
       (collarGeom : PlanarBoundaryAnnulusCollarGeometry emb) :
       Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
   ```

## Documented theorems

The following theorems capture the main claims. The countergraph obstruction is proved by
showing that the graph is a matching: walks remain inside one two-vertex component, trails have
length at most one, and a nonempty closed facial trail would contradict acyclicity.
-/

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusWitnessRegression
open Theorem49PlanarBoundaryAnnulusHonestGeometryRegression

/-!
### Main negative result: counterCollarGeometry cannot admit honest source
-/

/-- The unique matching partner of a vertex in `counterGraph`. -/
def counterMate (v : Fin 16) : Fin 16 :=
  match v.1 with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2
  | 4 => 5
  | 5 => 4
  | 6 => 7
  | 7 => 6
  | 8 => 9
  | 9 => 8
  | 10 => 11
  | 11 => 10
  | 12 => 13
  | 13 => 12
  | 14 => 15
  | 15 => 14
  | _ => 0

/-- Every neighbor of a vertex in the regression countergraph is its matching
partner. -/
theorem counterGraph_adj_left_eq_counterMate {u v : Fin 16}
    (h : counterGraph.Adj u v) : u = counterMate v := by
  let e : counterGraph.edgeSet := ⟨s(u, v), (SimpleGraph.mem_edgeSet counterGraph).2 h⟩
  rcases edge_eq_cases e with he | he | he | he | he | he | he | he
  · have hval : s(u, v) = s(0, 1) := by
      simpa [e, eo] using congr_arg Subtype.val he
    rw [Sym2.eq, Sym2.rel_iff] at hval
    rcases hval with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · have hval : s(u, v) = s(2, 3) := by
      simpa [e, ep] using congr_arg Subtype.val he
    rw [Sym2.eq, Sym2.rel_iff] at hval
    rcases hval with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · have hval : s(u, v) = s(4, 5) := by
      simpa [e, eqEdge] using congr_arg Subtype.val he
    rw [Sym2.eq, Sym2.rel_iff] at hval
    rcases hval with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · have hval : s(u, v) = (s(6, 7) : Sym2 (Fin 16)) := by
      simpa [e, er1] using congr_arg Subtype.val he
    rw [Sym2.eq, Sym2.rel_iff] at hval
    rcases hval with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · have hval : s(u, v) = (s(8, 9) : Sym2 (Fin 16)) := by
      simpa [e, er2] using congr_arg Subtype.val he
    rw [Sym2.eq, Sym2.rel_iff] at hval
    rcases hval with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · have hval : s(u, v) = s(10, 11) := by
      simpa [e, eiq] using congr_arg Subtype.val he
    rw [Sym2.eq, Sym2.rel_iff] at hval
    rcases hval with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · have hval : s(u, v) = s(12, 13) := by
      simpa [e, ei1] using congr_arg Subtype.val he
    rw [Sym2.eq, Sym2.rel_iff] at hval
    rcases hval with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · have hval : s(u, v) = s(14, 15) := by
      simpa [e, ei2] using congr_arg Subtype.val he
    rw [Sym2.eq, Sym2.rel_iff] at hval
    rcases hval with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- In the regression countergraph, every edge stays inside one two-vertex
matching component. -/
theorem counterGraph_adj_pair_eq {u v : Fin 16}
    (h : counterGraph.Adj u v) : u.1 / 2 = v.1 / 2 := by
  rw [counterGraph_adj_left_eq_counterMate h]
  fin_cases v <;> rfl

/-- Walks in the regression countergraph cannot leave their matching component. -/
theorem counterGraph_walk_pair_eq {u v : Fin 16}
    (p : counterGraph.Walk u v) : u.1 / 2 = v.1 / 2 := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
      exact (counterGraph_adj_pair_eq h).trans ih

/-- The counterGraph used in counterCollarGeometry is disconnected (has multiple connected
components). This can be verified by noting that vertices 0 and 2 are in separate components
(0 is only adjacent to 1, and 2 is only adjacent to 3, with no path between them). -/
theorem counterGraph_not_connected :
    ¬ Theorem49PlanarBoundaryAnnulusWitnessRegression.counterGraph.Connected := by
  intro hconn
  have ⟨p⟩ := hconn 0 2
  have hp := counterGraph_walk_pair_eq p
  norm_num at hp

/-- Two consecutive edges in the regression matching force the third vertex to
be the first one. -/
theorem counterGraph_adj_adj_eq {a b c : Fin 16}
    (hab : counterGraph.Adj a b) (hbc : counterGraph.Adj b c) : a = c :=
  (counterGraph_adj_left_eq_counterMate hab).trans
    (counterGraph_adj_left_eq_counterMate hbc.symm).symm

/-- A trail in the regression matching has length at most one. -/
theorem counterGraph_walk_length_le_one {v w : Fin 16}
    (p : counterGraph.Walk v w) (htrail : p.IsTrail) : p.length ≤ 1 := by
  cases p with
  | nil => simp
  | cons h₁ p₁ =>
      cases p₁ with
      | nil => simp
      | cons h₂ p₂ =>
          exfalso
          have hnodup :
              (SimpleGraph.Walk.cons h₁ (SimpleGraph.Walk.cons h₂ p₂)).edges.Nodup := by
            simpa [SimpleGraph.Walk.isTrail_def] using htrail
          have hx := counterGraph_adj_adj_eq h₁ h₂
          simp [SimpleGraph.Walk.edges_cons, hx] at hnodup

/-- The regression countergraph is a finite matching, hence acyclic. -/
theorem counterGraph_isAcyclic : counterGraph.IsAcyclic := by
  intro v c hc
  have hle : c.length ≤ 1 := counterGraph_walk_length_le_one c hc.isTrail
  have hge : 3 ≤ c.length := hc.three_le_length
  omega

/-- Face f0 in counterEmbedding has boundary {eo, ep} where eo = s(0,1) and ep = s(2,3).
These edges have disjoint vertex sets, and since the graph is disconnected, there is no
walk that can traverse both edges. -/
theorem not_admits_faceBoundaryClosedWalk_counterEmbedding_fa :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk counterEmbedding fa) := by
  rintro ⟨data⟩
  have htrail : data.walk.IsTrail := by
    simpa [SimpleGraph.Walk.isTrail_def] using data.hnodup_edges
  have hpath : data.walk.IsPath := (counterGraph_isAcyclic.isPath_iff_isTrail data.walk).2 htrail
  have hnil : data.walk = .nil := (SimpleGraph.Walk.isPath_iff_eq_nil data.walk).1 hpath
  have hnonempty : 0 < data.walk.length := data.hnonempty
  rw [hnil] at hnonempty
  simp at hnonempty

/-- Since face f0 does not admit a facial closed walk, the counterEmbedding cannot admit
a closed-walk embedding data structure (which requires every face to have a closed walk). -/
theorem not_admits_closedWalkEmbeddingData_counterEmbedding :
    ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData counterEmbedding) := by
  intro ⟨data⟩
  exact not_admits_faceBoundaryClosedWalk_counterEmbedding_fa ⟨data.faceBoundaryClosedWalk fa⟩

/-- The regression countergraph has an edge, so the generic acyclic obstruction applies at
graph level. -/
theorem counterGraph_edgeSet_nonempty : Nonempty counterGraph.edgeSet :=
  ⟨eo⟩

/-- No embedding of the regression matching graph can carry an honest closed-walk annulus
boundary source. -/
theorem not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_counterGraph :
    ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource counterGraph := by
  exact
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      counterGraph_isAcyclic counterGraph_edgeSet_nonempty

/-- **Main result**: The counterCollarGeometry obstruction (which violates previous-boundary
witness geometry) cannot admit a honest closed-walk source.

This establishes that honest sources rule out the known obstruction to deriving previous-boundary
witness from collar geometry. -/
theorem not_admits_honestSource_counterCollarGeometry :
    ¬ Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource counterEmbedding) := by
  intro ⟨source⟩
  exact not_admits_closedWalkEmbeddingData_counterEmbedding ⟨source.closedWalks⟩

/-!
### Contrast with the positive example

Recall from `Theorem49PlanarBoundaryAnnulusHonestGeometryRegression` that `diamondWithTriangle`
DOES admit both an honest source (`diamondWithTriangleHonestSource`) and previous-boundary witness
geometry (`diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry`).

The key difference: `diamondWithTriangle` has a **connected** graph where facial closed walks
can actually traverse the face boundaries.
-/

/-!
## Summary of investigation status

**Question**: Can honest closed-walk sources force previous-boundary witness geometry?

**Finding**: The known counterexample to deriving previous-boundary witness from basic collar
geometry (`counterCollarGeometry`) is **ruled out** by the honest source requirement.

**Mechanism**: Honest sources require facial closed walks, which require graph connectivity.
The counterexample uses a disconnected graph where facial closed walks cannot exist.

**Next step**: Prove that honest sources + collar geometry ⟹ previous-boundary witness.
The key will be showing that the connectivity forced by honest sources prevents witness edges
from lying on "wrong" (later rather than previous) boundary cycles.

**Status**: The countergraph obstruction is now formal. The remaining route work is:
1. Generalizing the face-boundary connectivity properties forced by facial closed walks
2. Proving these properties + collar geometry imply previous-boundary witness
-/

end Mettapedia.GraphTheory.FourColor
