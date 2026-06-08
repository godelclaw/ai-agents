import Mettapedia.GraphTheory.PlanarEmbeddingWithBoundary
import Mathlib.Data.List.Chain
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.List.Rotate

namespace Mettapedia.GraphTheory

universe u

variable {V : Type u} [DecidableEq V]

/-- Raw shared-endpoint adjacency on graph edges. This is the generic edge-order relation used
when an embedding supplies an explicit list order for each face boundary. -/
def planarEmbeddingBoundaryEdgeEndpointAdj {G : SimpleGraph V} (e f : G.edgeSet) : Prop :=
  e ≠ f ∧ ∃ v : V, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)

/-- A walk-based face boundary for one embedded face: the face boundary is given as an actual
closed simple walk in the graph. This is the most primitive source object for boundary order,
directly using Mathlib's SimpleGraph.Walk structure. It serves as a foundation that can be
lowered to more abstract edge-list and vertex-list representations. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (f : {f // f ∈ emb.faces}) where
  /-- The starting (and ending) vertex of the closed walk -/
  baseVertex : V
  /-- The closed walk representing the face boundary -/
  walk : G.Walk baseVertex baseVertex
  /-- The walk is nonempty (has at least one edge) -/
  hnonempty : walk.length > 0
  /-- The walk has no repeated edges (is simple as a walk of edges) -/
  hnodup_edges : walk.edges.Nodup
  /-- Every edge traversed by the walk belongs to the face boundary. We record this via the
  underlying `Sym2` edge values because `walk.edges` is a list of graph edges before they are
  repackaged as `G.edgeSet` elements. -/
  hedge_sub : ∀ e ∈ walk.edges, e ∈ (emb.faceBoundary f.1).image Subtype.val
  /-- Every edge in the face boundary appears in the walk -/
  hface_sub : ∀ e ∈ emb.faceBoundary f.1, (e : Sym2 V) ∈ walk.edges

/-- Stronger local data on top of `PlaneEmbeddingWithBoundary`: for each actual embedded face,
the boundary edges are listed exactly once in an endpoint-sharing order. This is the generic
order-bearing source object needed by the FourColor face-boundary run layer. -/
structure PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  faceBoundaryOrder : {f // f ∈ emb.faces} → List G.edgeSet
  hchain : ∀ f : {f // f ∈ emb.faces},
    List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj (faceBoundaryOrder f)
  hnodup : ∀ f : {f // f ∈ emb.faces}, (faceBoundaryOrder f).Nodup
  hmem : ∀ (f : {f // f ∈ emb.faces}) (e : G.edgeSet),
    e ∈ faceBoundaryOrder f ↔ e ∈ emb.faceBoundary f.1

/-- A cyclic strengthening of `OrderedFaceBoundaryData`: in addition to listing each face boundary
once in endpoint-sharing order, the list closes up at the ends. This is closer to genuine
embedding-side face-boundary order than a merely linear chain, while still staying within the
current edge-list abstraction. -/
structure PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    extends PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb where
  hwrap : ∀ f : {f // f ∈ emb.faces}, ∀ first last : G.edgeSet,
    (faceBoundaryOrder f).head? = some first →
      (faceBoundaryOrder f).getLast? = some last →
        planarEmbeddingBoundaryEdgeEndpointAdj last first

/-- A source-facing ordered boundary run for one embedded face: the face boundary is listed
exactly once as a chain of distinct graph edges, where consecutive edges share a primal endpoint.
This is the smallest pure edge-order interface that can be built on top of the current finite-set
embedding API. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryEndpointRun {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (f : {f // f ∈ emb.faces}) where
  run : List G.edgeSet
  hchain : List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj run
  hnodup : run.Nodup
  hmem : ∀ e : G.edgeSet, e ∈ run ↔ e ∈ emb.faceBoundary f.1

/-- A cyclic face-boundary run for one embedded face: the full face boundary is listed exactly
once, consecutive edges share a primal endpoint, and the last edge also shares a primal endpoint
with the first. The closure is expressed by requiring the chain relation on the list obtained by
appending the first edge to the end. This is the closest pure local boundary-walk object to honest
embedding-side cyclic face order that can be phrased over the current edge-list API. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryClosedEndpointRun {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (f : {f // f ∈ emb.faces}) where
  run : List G.edgeSet
  hclosed : List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj (run ++ run.head?.toList)
  hnodup : run.Nodup
  hmem : ∀ e : G.edgeSet, e ∈ run ↔ e ∈ emb.faceBoundary f.1

/-- A closed face-boundary run forgets to its linear endpoint-sharing part. -/
theorem PlaneEmbeddingWithBoundary.FaceBoundaryClosedEndpointRun.hchain
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {f : {f // f ∈ emb.faces}}
    (run : PlaneEmbeddingWithBoundary.FaceBoundaryClosedEndpointRun emb f) :
    List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj run.run := by
  simpa using List.IsChain.left_of_append run.hclosed

/-- The closure of a closed face-boundary run recovers the endpoint-sharing relation between its
last and first edges whenever both exist. -/
theorem PlaneEmbeddingWithBoundary.FaceBoundaryClosedEndpointRun.hwrap
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {f : {f // f ∈ emb.faces}}
    (run : PlaneEmbeddingWithBoundary.FaceBoundaryClosedEndpointRun emb f)
    {first last : G.edgeSet}
    (hfirst : run.run.head? = some first)
    (hlast : run.run.getLast? = some last) :
    planarEmbeddingBoundaryEdgeEndpointAdj last first := by
  have hbridge := (List.isChain_append.1 run.hclosed).2.2
  exact hbridge last (by simp [Option.mem_def, hlast]) first (by simp [Option.mem_def, hfirst])

/-- A closed face-boundary run repackaged as its linear endpoint-sharing part. -/
def PlaneEmbeddingWithBoundary.FaceBoundaryClosedEndpointRun.toFaceBoundaryEndpointRun
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {f : {f // f ∈ emb.faces}}
    (run : PlaneEmbeddingWithBoundary.FaceBoundaryClosedEndpointRun emb f) :
    PlaneEmbeddingWithBoundary.FaceBoundaryEndpointRun emb f where
  run := run.run
  hchain := run.hchain
  hnodup := run.hnodup
  hmem := run.hmem

/-- A bundled pure face-boundary ordering witness: every embedded face is equipped with one
explicit ordered endpoint-sharing run of its full boundary. This isolates the order-only geometry
burden from any later selected-boundary or annulus-specific structure. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  faceBoundaryRun :
    ∀ f : {f // f ∈ emb.faces}, PlaneEmbeddingWithBoundary.FaceBoundaryEndpointRun emb f

/-- A bundled cyclic face-boundary run witness: every embedded face is equipped with one explicit
closed boundary run. This is the bundled pure boundary-walk source layer corresponding to cyclic
ordered face-boundary data. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  faceBoundaryClosedRun :
    ∀ f : {f // f ∈ emb.faces}, PlaneEmbeddingWithBoundary.FaceBoundaryClosedEndpointRun emb f

/-- A pure cyclic alternating boundary-walk witness for one embedded face: in addition to the
closed edge run, we store one explicit cyclic list of primal vertices such that each boundary edge
is incident both to its own listed vertex and to the next listed vertex in cyclic order. This is
closer to an honest embedding-side facial walk than the edge-only closed-run layer. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalk {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (f : {f // f ∈ emb.faces})
    extends PlaneEmbeddingWithBoundary.FaceBoundaryClosedEndpointRun emb f where
  vertices : List V
  hincident_here :
    List.Forall₂ (fun v e => v ∈ (e : Sym2 V)) vertices run
  hincident_next :
    List.Forall₂ (fun v e => v ∈ (e : Sym2 V)) vertices (run.rotate 1)

/-- A bundled cyclic alternating boundary-walk witness: every embedded face carries one explicit
cyclic edge/vertex walk. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  faceBoundaryClosedVertexWalk :
    ∀ f : {f // f ∈ emb.faces}, PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalk emb f

/-- Forget the explicit cyclic primal vertices and retain only the closed edge run. -/
def PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry.toFaceBoundaryClosedRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry emb where
  faceBoundaryClosedRun := fun f => (geom.faceBoundaryClosedVertexWalk f).toFaceBoundaryClosedEndpointRun

/-- Ordered face-boundary data repackaged as a `FaceBoundaryEndpointRun`. -/
def PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData.faceBoundaryRun
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb)
    (f : {f // f ∈ emb.faces}) :
    PlaneEmbeddingWithBoundary.FaceBoundaryEndpointRun emb f where
  run := data.faceBoundaryOrder f
  hchain := data.hchain f
  hnodup := data.hnodup f
  hmem := data.hmem f

/-- Ordered face-boundary data lowers directly to the bundled face-boundary run geometry
package. -/
def PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData.toFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry emb where
  faceBoundaryRun := data.faceBoundaryRun

/-- Cyclic ordered face-boundary data also lowers to the bundled pure run geometry package. -/
def PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData.toFaceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry emb :=
  data.toOrderedFaceBoundaryData.toFaceBoundaryRunGeometry

/-- Cyclic ordered face-boundary data repackaged as a closed face-boundary run. -/
def PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData.faceBoundaryClosedRun
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb)
    (f : {f // f ∈ emb.faces}) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedEndpointRun emb f where
  run := data.faceBoundaryOrder f
  hclosed := by
    cases hrun : data.faceBoundaryOrder f with
    | nil =>
        simp
    | cons a tl =>
        have hchain : List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj (a :: tl) := by
          simpa [hrun] using data.hchain f
        have hbridge :
            ∀ x ∈ (a :: tl).getLast?, ∀ y ∈ ([a] : List G.edgeSet).head?,
              planarEmbeddingBoundaryEdgeEndpointAdj x y := by
          intro x hx y hy
          have hy' : a = y := by
            simpa [Option.mem_def] using hy
          subst y
          have hx' : (a :: tl).getLast? = some x := by
            simpa [Option.mem_def] using hx
          exact data.hwrap f a x (by simp [hrun]) (by simpa [hrun] using hx')
        simpa [hrun] using hchain.append (List.isChain_singleton a) hbridge
  hnodup := data.hnodup f
  hmem := data.hmem f

/-- Cyclic ordered face-boundary data lowers directly to the bundled closed boundary-run
geometry package. -/
def PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData.toFaceBoundaryClosedRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry emb where
  faceBoundaryClosedRun := data.faceBoundaryClosedRun

/-- Bundled face-boundary run geometry can be repackaged back into ordered face-boundary data. -/
def PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry.toOrderedFaceBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry emb) :
    PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb where
  faceBoundaryOrder := fun f => (geom.faceBoundaryRun f).run
  hchain := fun f => (geom.faceBoundaryRun f).hchain
  hnodup := fun f => (geom.faceBoundaryRun f).hnodup
  hmem := fun f => (geom.faceBoundaryRun f).hmem

/-- Bundled closed boundary-run geometry can be repackaged back into cyclic ordered face-boundary
data. -/
def PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry.toCyclicOrderedFaceBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry emb) :
    PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb where
  faceBoundaryOrder := fun f => (geom.faceBoundaryClosedRun f).run
  hchain := fun f => (geom.faceBoundaryClosedRun f).hchain
  hnodup := fun f => (geom.faceBoundaryClosedRun f).hnodup
  hmem := fun f => (geom.faceBoundaryClosedRun f).hmem
  hwrap := fun f first last hfirst hlast =>
    (geom.faceBoundaryClosedRun f).hwrap (first := first) (last := last) hfirst hlast

/-- Ordered face-boundary data together with an explicit chosen shared primal endpoint for each
adjacent pair of boundary edges in the listed order. This is a proof-relevant linear boundary-walk
surrogate that sits closer to honest embedding-side facial walks than the edge-only order layer. -/
structure PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    extends PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb where
  boundaryStepVertex :
    ∀ f : {f // f ∈ emb.faces}, ∀ e₁ e₂ : G.edgeSet,
      [e₁, e₂] <:+: faceBoundaryOrder f → V
  hboundaryStepVertex_left :
    ∀ (f : {f // f ∈ emb.faces}) (e₁ e₂ : G.edgeSet)
      (hpair : [e₁, e₂] <:+: faceBoundaryOrder f),
        boundaryStepVertex f e₁ e₂ hpair ∈ (e₁ : Sym2 V)
  hboundaryStepVertex_right :
    ∀ (f : {f // f ∈ emb.faces}) (e₁ e₂ : G.edgeSet)
      (hpair : [e₁, e₂] <:+: faceBoundaryOrder f),
        boundaryStepVertex f e₁ e₂ hpair ∈ (e₂ : Sym2 V)

/-- Cyclic ordered face-boundary data together with an explicit chosen shared primal endpoint for
each adjacent pair in the closed cyclic boundary list. This is a proof-relevant cyclic
boundary-walk surrogate. -/
structure PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    extends PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb where
  boundaryStepVertex :
    ∀ f : {f // f ∈ emb.faces}, ∀ e₁ e₂ : G.edgeSet,
      [e₁, e₂] <:+: (faceBoundaryOrder f ++ (faceBoundaryOrder f).head?.toList) → V
  hboundaryStepVertex_left :
    ∀ (f : {f // f ∈ emb.faces}) (e₁ e₂ : G.edgeSet)
      (hpair : [e₁, e₂] <:+: (faceBoundaryOrder f ++ (faceBoundaryOrder f).head?.toList)),
        boundaryStepVertex f e₁ e₂ hpair ∈ (e₁ : Sym2 V)
  hboundaryStepVertex_right :
    ∀ (f : {f // f ∈ emb.faces}) (e₁ e₂ : G.edgeSet)
      (hpair : [e₁, e₂] <:+: (faceBoundaryOrder f ++ (faceBoundaryOrder f).head?.toList)),
        boundaryStepVertex f e₁ e₂ hpair ∈ (e₂ : Sym2 V)

/-- Any adjacent pair of edges occurring in an ordered face-boundary list satisfies the raw
shared-endpoint adjacency relation. -/
theorem PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData.boundaryEdgeEndpointAdj_of_pairInfix
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb)
    {f : {f // f ∈ emb.faces}} {e₁ e₂ : G.edgeSet}
    (hpair : [e₁, e₂] <:+: data.faceBoundaryOrder f) :
    planarEmbeddingBoundaryEdgeEndpointAdj e₁ e₂ := by
  exact (List.isChain_pair.1 ((data.hchain f).infix hpair))

/-- Any adjacent pair of edges occurring in the closed cyclic boundary list satisfies the raw
shared-endpoint adjacency relation. -/
theorem PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData.boundaryEdgeEndpointAdj_of_pairInfix
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb)
    {f : {f // f ∈ emb.faces}} {e₁ e₂ : G.edgeSet}
    (hpair : [e₁, e₂] <:+:
      (data.faceBoundaryOrder f ++ (data.faceBoundaryOrder f).head?.toList)) :
    planarEmbeddingBoundaryEdgeEndpointAdj e₁ e₂ := by
  exact (List.isChain_pair.1 ((data.faceBoundaryClosedRun f).hclosed.infix hpair))

/-- A `Forall₂` proof of endpoint-sharing edge adjacency yields an explicit list of shared primal
endpoints, one for each aligned pair. -/
private theorem exists_boundaryStepVerticesOfForall₂
    {V : Type u} {G : SimpleGraph V} {as bs : List G.edgeSet}
    (hpair : List.Forall₂ planarEmbeddingBoundaryEdgeEndpointAdj as bs) :
    ∃ vs : List V,
      List.Forall₂ (fun v e => v ∈ (e : Sym2 V)) vs as ∧
        List.Forall₂ (fun v e => v ∈ (e : Sym2 V)) vs bs := by
  induction hpair with
  | nil =>
      exact ⟨[], .nil, .nil⟩
  | @cons a b l₁ l₂ hab htail ih =>
      rcases ih with ⟨vs, hleft, hright⟩
      rcases hab.2 with ⟨v, hva, hvb⟩
      exact ⟨v :: vs, .cons hva hleft, .cons hvb hright⟩

/-- Choose one shared primal endpoint for each aligned pair in a `Forall₂` proof of
endpoint-sharing edge adjacency. This converts proof-only adjacency data into an explicit list of
boundary step vertices. -/
private noncomputable def chooseBoundaryStepVerticesOfForall₂
    {V : Type u} {G : SimpleGraph V} {as bs : List G.edgeSet}
    (hpair : List.Forall₂ planarEmbeddingBoundaryEdgeEndpointAdj as bs) : List V :=
  Classical.choose (exists_boundaryStepVerticesOfForall₂ hpair)

/-- The chosen step vertices lie on the left edge list from the original `Forall₂` proof. -/
private theorem chooseBoundaryStepVerticesOfForall₂_left
    {V : Type u} {G : SimpleGraph V} {as bs : List G.edgeSet}
    (hpair : List.Forall₂ planarEmbeddingBoundaryEdgeEndpointAdj as bs) :
    List.Forall₂ (fun v e => v ∈ (e : Sym2 V))
      (chooseBoundaryStepVerticesOfForall₂ hpair) as :=
  (Classical.choose_spec (exists_boundaryStepVerticesOfForall₂ hpair)).1

/-- The chosen step vertices lie on the right edge list from the original `Forall₂` proof. -/
private theorem chooseBoundaryStepVerticesOfForall₂_right
    {V : Type u} {G : SimpleGraph V} {as bs : List G.edgeSet}
    (hpair : List.Forall₂ planarEmbeddingBoundaryEdgeEndpointAdj as bs) :
    List.Forall₂ (fun v e => v ∈ (e : Sym2 V))
      (chooseBoundaryStepVerticesOfForall₂ hpair) bs :=
  (Classical.choose_spec (exists_boundaryStepVerticesOfForall₂ hpair)).2

/-- Ordered face-boundary data can be upgraded to proof-relevant boundary-step vertex data by
choosing one shared endpoint for each adjacent pair. -/
noncomputable def PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData.toOrderedFaceBoundaryVertexData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb) :
    PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexData emb where
  faceBoundaryOrder := data.faceBoundaryOrder
  hchain := data.hchain
  hnodup := data.hnodup
  hmem := data.hmem
  boundaryStepVertex := fun f e₁ e₂ hpair =>
    Classical.choose (data.boundaryEdgeEndpointAdj_of_pairInfix hpair).2
  hboundaryStepVertex_left := by
    intro f e₁ e₂ hpair
    exact (Classical.choose_spec (data.boundaryEdgeEndpointAdj_of_pairInfix hpair).2).1
  hboundaryStepVertex_right := by
    intro f e₁ e₂ hpair
    exact (Classical.choose_spec (data.boundaryEdgeEndpointAdj_of_pairInfix hpair).2).2

/-- Cyclic ordered face-boundary data can be upgraded to proof-relevant cyclic boundary-step
vertex data by choosing one shared endpoint for each adjacent pair in the closed cyclic list. -/
noncomputable def PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData.toCyclicOrderedFaceBoundaryVertexData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb) :
    PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexData emb where
  faceBoundaryOrder := data.faceBoundaryOrder
  hchain := data.hchain
  hnodup := data.hnodup
  hmem := data.hmem
  hwrap := data.hwrap
  boundaryStepVertex := fun f e₁ e₂ hpair =>
    Classical.choose (data.boundaryEdgeEndpointAdj_of_pairInfix hpair).2
  hboundaryStepVertex_left := by
    intro f e₁ e₂ hpair
    exact (Classical.choose_spec (data.boundaryEdgeEndpointAdj_of_pairInfix hpair).2).1
  hboundaryStepVertex_right := by
    intro f e₁ e₂ hpair
    exact (Classical.choose_spec (data.boundaryEdgeEndpointAdj_of_pairInfix hpair).2).2

/-- Ordered face-boundary data together with one explicit ordered list of shared primal vertices
between consecutive edges. This is closer to an honest facial boundary walk than the pair-indexed
chooser interface because the shared vertices are stored in the same order as the boundary edges.
-/
structure PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexSequenceData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    extends PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb where
  faceBoundaryStepVertices : ∀ _ : {f // f ∈ emb.faces}, List V
  hstep_left :
    ∀ f : {f // f ∈ emb.faces},
      List.Forall₂ (fun v e => v ∈ (e : Sym2 V))
        (faceBoundaryStepVertices f) ((faceBoundaryOrder f).dropLast)
  hstep_right :
    ∀ f : {f // f ∈ emb.faces},
      List.Forall₂ (fun v e => v ∈ (e : Sym2 V))
        (faceBoundaryStepVertices f) (faceBoundaryOrder f).tail

/-- Cyclic ordered face-boundary data together with one explicit cyclic list of shared primal
vertices between each edge and its successor in cyclic order. This is the current closest source
proxy to an honest cyclic facial boundary walk over the weak finite-set embedding API. -/
structure PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G)
    extends PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb where
  faceBoundaryStepVertices : ∀ _ : {f // f ∈ emb.faces}, List V
  hstep_left :
    ∀ f : {f // f ∈ emb.faces},
      List.Forall₂ (fun v e => v ∈ (e : Sym2 V))
        (faceBoundaryStepVertices f) (faceBoundaryOrder f)
  hstep_right :
    ∀ f : {f // f ∈ emb.faces},
      List.Forall₂ (fun v e => v ∈ (e : Sym2 V))
        (faceBoundaryStepVertices f) ((faceBoundaryOrder f).rotate 1)

/-- Ordered face-boundary data upgrades canonically to an explicit boundary-step vertex sequence
by choosing one shared endpoint along each consecutive edge pair in the boundary order. -/
noncomputable def
    PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData.toOrderedFaceBoundaryVertexSequenceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb) :
    PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexSequenceData emb where
  faceBoundaryOrder := data.faceBoundaryOrder
  hchain := data.hchain
  hnodup := data.hnodup
  hmem := data.hmem
  faceBoundaryStepVertices := fun f =>
    chooseBoundaryStepVerticesOfForall₂ ((List.isChain_iff_forall₂.1 (data.hchain f)))
  hstep_left := by
    intro f
    exact chooseBoundaryStepVerticesOfForall₂_left ((List.isChain_iff_forall₂.1 (data.hchain f)))
  hstep_right := by
    intro f
    exact chooseBoundaryStepVerticesOfForall₂_right ((List.isChain_iff_forall₂.1 (data.hchain f)))

/-- A cyclic ordered face-boundary list induces raw endpoint-sharing adjacency between each edge
and its cyclic successor. -/
private theorem PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData.forall₂_boundaryAdj_rotate
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb)
    (f : {f // f ∈ emb.faces}) :
    List.Forall₂ planarEmbeddingBoundaryEdgeEndpointAdj
      (data.faceBoundaryOrder f) ((data.faceBoundaryOrder f).rotate 1) := by
  have hclosed₀ :
      List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj
        (data.faceBoundaryOrder f ++ (data.faceBoundaryOrder f).head?.toList) :=
    (data.faceBoundaryClosedRun f).hclosed
  cases hrun : data.faceBoundaryOrder f with
  | nil =>
      simp
  | cons a tl =>
      have hclosed : List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj ((a :: tl) ++ [a]) := by
        simpa [hrun] using hclosed₀
      have hpair :
          List.Forall₂ planarEmbeddingBoundaryEdgeEndpointAdj (a :: tl) (tl ++ [a]) := by
        exact List.isChain_cons_append_singleton_iff_forall₂.1 hclosed
      simpa using hpair

/-- Cyclic ordered face-boundary data upgrades canonically to an explicit cyclic boundary-step
vertex sequence by choosing one shared endpoint between each edge and its cyclic successor. -/
noncomputable def
    PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData.toCyclicOrderedFaceBoundaryVertexSequenceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb) :
    PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData emb where
  faceBoundaryOrder := data.faceBoundaryOrder
  hchain := data.hchain
  hnodup := data.hnodup
  hmem := data.hmem
  hwrap := data.hwrap
  faceBoundaryStepVertices := fun f =>
    chooseBoundaryStepVerticesOfForall₂ (data.forall₂_boundaryAdj_rotate f)
  hstep_left := by
    intro f
    exact chooseBoundaryStepVerticesOfForall₂_left (data.forall₂_boundaryAdj_rotate f)
  hstep_right := by
    intro f
    exact chooseBoundaryStepVerticesOfForall₂_right (data.forall₂_boundaryAdj_rotate f)

/-- Cyclic ordered face-boundary vertex-sequence data repackaged as an explicit cyclic
edge/vertex boundary walk. -/
def PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData.faceBoundaryClosedVertexWalk
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData emb)
    (f : {f // f ∈ emb.faces}) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalk emb f where
  toFaceBoundaryClosedEndpointRun := data.faceBoundaryClosedRun f
  vertices := data.faceBoundaryStepVertices f
  hincident_here := data.hstep_left f
  hincident_next := data.hstep_right f

/-- Cyclic ordered face-boundary vertex-sequence data lowers directly to the bundled explicit
cyclic edge/vertex boundary-walk geometry. -/
def PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData.toFaceBoundaryClosedVertexWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry emb where
  faceBoundaryClosedVertexWalk := data.faceBoundaryClosedVertexWalk

/-- Bundled explicit cyclic edge/vertex boundary-walk geometry can be repackaged back into cyclic
ordered face-boundary vertex-sequence data. -/
def PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry.toCyclicOrderedFaceBoundaryVertexSequenceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry emb) :
    PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData emb where
  faceBoundaryOrder := fun f => (geom.faceBoundaryClosedVertexWalk f).run
  hchain := fun f => (geom.faceBoundaryClosedVertexWalk f).hchain
  hnodup := fun f => (geom.faceBoundaryClosedVertexWalk f).hnodup
  hmem := fun f => (geom.faceBoundaryClosedVertexWalk f).hmem
  hwrap := by
    intro f first last hfirst hlast
    exact (geom.faceBoundaryClosedVertexWalk f).hwrap (first := first) (last := last) hfirst hlast
  faceBoundaryStepVertices := fun f => (geom.faceBoundaryClosedVertexWalk f).vertices
  hstep_left := fun f => (geom.faceBoundaryClosedVertexWalk f).hincident_here
  hstep_right := fun f => (geom.faceBoundaryClosedVertexWalk f).hincident_next

/-- Graph-level existence form of the pure face-boundary order target. -/
def AdmitsFaceBoundaryRunGeometry (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry emb)

/-- Graph-level existence form of the bundled cyclic boundary-run target. -/
def AdmitsFaceBoundaryClosedRunGeometry (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry emb)

/-- Graph-level existence form of the bundled explicit cyclic edge/vertex boundary-walk target.
-/
def AdmitsFaceBoundaryClosedVertexWalkGeometry (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry emb)

/-- Graph-level existence form of the explicit cyclic boundary-step vertex sequence interface. -/
def AdmitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData emb)

/-- Graph-level existence form of the explicit ordered boundary-step vertex sequence interface. -/
def AdmitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexSequenceData emb)

/-- Graph-level existence form of the proof-relevant cyclic ordered face-boundary vertex
interface. -/
def AdmitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexData emb)

/-- Graph-level existence form of the proof-relevant ordered face-boundary vertex interface. -/
def AdmitsOrderedFaceBoundaryVertexPlaneEmbeddingData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexData emb)

/-- Graph-level existence form of the cyclic ordered face-boundary interface. -/
def AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb)

/-- Graph-level existence form of the stronger ordered face-boundary interface. -/
def AdmitsOrderedFaceBoundaryPlaneEmbeddingData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb)

theorem nonempty_cyclicOrderedFaceBoundaryData_implies_nonempty_orderedFaceBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb) →
      Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb) := by
  rintro ⟨data⟩
  exact ⟨data.toOrderedFaceBoundaryData⟩

theorem nonempty_orderedFaceBoundaryData_iff_nonempty_orderedFaceBoundaryVertexData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb) ↔
      Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexData emb) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toOrderedFaceBoundaryVertexData⟩
  · rintro ⟨data⟩
    exact ⟨data.toOrderedFaceBoundaryData⟩

theorem nonempty_orderedFaceBoundaryData_iff_nonempty_orderedFaceBoundaryVertexSequenceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb) ↔
      Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryVertexSequenceData emb) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toOrderedFaceBoundaryVertexSequenceData⟩
  · rintro ⟨data⟩
    exact ⟨data.toOrderedFaceBoundaryData⟩

theorem nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb) ↔
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry emb) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toFaceBoundaryClosedRunGeometry⟩
  · rintro ⟨geom⟩
    exact ⟨geom.toCyclicOrderedFaceBoundaryData⟩

theorem nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_cyclicOrderedFaceBoundaryVertexData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb) ↔
      Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexData emb) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toCyclicOrderedFaceBoundaryVertexData⟩
  · rintro ⟨data⟩
    exact ⟨data.toCyclicOrderedFaceBoundaryData⟩

theorem nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_cyclicOrderedFaceBoundaryVertexSequenceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb) ↔
      Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData emb) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toCyclicOrderedFaceBoundaryVertexSequenceData⟩
  · rintro ⟨data⟩
    exact ⟨data.toCyclicOrderedFaceBoundaryData⟩

theorem
    nonempty_cyclicOrderedFaceBoundaryVertexSequenceData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryVertexSequenceData emb) ↔
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry emb) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toFaceBoundaryClosedVertexWalkGeometry⟩
  · rintro ⟨geom⟩
    exact ⟨geom.toCyclicOrderedFaceBoundaryVertexSequenceData⟩

theorem nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb) ↔
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry emb) := by
  rw
    [nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_cyclicOrderedFaceBoundaryVertexSequenceData,
      nonempty_cyclicOrderedFaceBoundaryVertexSequenceData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry]

theorem nonempty_faceBoundaryClosedRunGeometry_iff_nonempty_faceBoundaryClosedVertexWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry emb) ↔
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry emb) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedRunGeometry,
    nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry]

theorem nonempty_orderedFaceBoundaryData_iff_nonempty_faceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData emb) ↔
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry emb) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toFaceBoundaryRunGeometry⟩
  · rintro ⟨geom⟩
    exact ⟨geom.toOrderedFaceBoundaryData⟩

theorem admitsFaceBoundaryRunGeometry_of_admitsOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsOrderedFaceBoundaryPlaneEmbeddingData G) :
    AdmitsFaceBoundaryRunGeometry G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toFaceBoundaryRunGeometry⟩⟩

theorem admitsFaceBoundaryClosedRunGeometry_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G) :
    AdmitsFaceBoundaryClosedRunGeometry G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toFaceBoundaryClosedRunGeometry⟩⟩

theorem
    admitsFaceBoundaryClosedVertexWalkGeometry_of_admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData G) :
    AdmitsFaceBoundaryClosedVertexWalkGeometry G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toFaceBoundaryClosedVertexWalkGeometry⟩⟩

theorem
    admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_of_admitsFaceBoundaryClosedVertexWalkGeometry
    {G : SimpleGraph V}
    (hG : AdmitsFaceBoundaryClosedVertexWalkGeometry G) :
    AdmitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, ⟨geom.toCyclicOrderedFaceBoundaryVertexSequenceData⟩⟩

theorem admitsOrderedFaceBoundaryPlaneEmbeddingData_of_admitsOrderedFaceBoundaryVertexPlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsOrderedFaceBoundaryVertexPlaneEmbeddingData G) :
    AdmitsOrderedFaceBoundaryPlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toOrderedFaceBoundaryData⟩⟩

theorem
    admitsOrderedFaceBoundaryPlaneEmbeddingData_of_admitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData G) :
    AdmitsOrderedFaceBoundaryPlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toOrderedFaceBoundaryData⟩⟩

theorem admitsOrderedFaceBoundaryVertexPlaneEmbeddingData_of_admitsOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsOrderedFaceBoundaryPlaneEmbeddingData G) :
    AdmitsOrderedFaceBoundaryVertexPlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toOrderedFaceBoundaryVertexData⟩⟩

theorem
    admitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_of_admitsOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsOrderedFaceBoundaryPlaneEmbeddingData G) :
    AdmitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toOrderedFaceBoundaryVertexSequenceData⟩⟩

theorem admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsFaceBoundaryClosedRunGeometry
    {G : SimpleGraph V}
    (hG : AdmitsFaceBoundaryClosedRunGeometry G) :
    AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, ⟨geom.toCyclicOrderedFaceBoundaryData⟩⟩

theorem
    admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData G) :
    AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toCyclicOrderedFaceBoundaryData⟩⟩

theorem
    admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData G) :
    AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toCyclicOrderedFaceBoundaryData⟩⟩

theorem
    admitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G) :
    AdmitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toCyclicOrderedFaceBoundaryVertexData⟩⟩

theorem
    admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G) :
    AdmitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toCyclicOrderedFaceBoundaryVertexSequenceData⟩⟩

theorem admitsFaceBoundaryClosedVertexWalkGeometry_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G) :
    AdmitsFaceBoundaryClosedVertexWalkGeometry G := by
  exact
    admitsFaceBoundaryClosedVertexWalkGeometry_of_admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData
      (admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
        hG)

theorem admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsFaceBoundaryClosedVertexWalkGeometry
    {G : SimpleGraph V}
    (hG : AdmitsFaceBoundaryClosedVertexWalkGeometry G) :
    AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G := by
  exact
    admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData
      (admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_of_admitsFaceBoundaryClosedVertexWalkGeometry
        hG)

theorem admitsFaceBoundaryClosedRunGeometry_of_admitsFaceBoundaryClosedVertexWalkGeometry
    {G : SimpleGraph V}
    (hG : AdmitsFaceBoundaryClosedVertexWalkGeometry G) :
    AdmitsFaceBoundaryClosedRunGeometry G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, ⟨geom.toFaceBoundaryClosedRunGeometry⟩⟩

theorem admitsFaceBoundaryClosedVertexWalkGeometry_of_admitsFaceBoundaryClosedRunGeometry
    {G : SimpleGraph V}
    (hG : AdmitsFaceBoundaryClosedRunGeometry G) :
    AdmitsFaceBoundaryClosedVertexWalkGeometry G := by
  exact
    admitsFaceBoundaryClosedVertexWalkGeometry_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
      (admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsFaceBoundaryClosedRunGeometry hG)

theorem admitsOrderedFaceBoundaryPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G) :
    AdmitsOrderedFaceBoundaryPlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toOrderedFaceBoundaryData⟩⟩

theorem admitsFaceBoundaryRunGeometry_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G) :
    AdmitsFaceBoundaryRunGeometry G := by
  exact
    admitsFaceBoundaryRunGeometry_of_admitsOrderedFaceBoundaryPlaneEmbeddingData
      (admitsOrderedFaceBoundaryPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
        hG)

theorem admitsFaceBoundaryRunGeometry_of_admitsFaceBoundaryClosedRunGeometry
    {G : SimpleGraph V}
    (hG : AdmitsFaceBoundaryClosedRunGeometry G) :
    AdmitsFaceBoundaryRunGeometry G := by
  exact
    admitsFaceBoundaryRunGeometry_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
      (admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsFaceBoundaryClosedRunGeometry hG)

theorem admitsOrderedFaceBoundaryPlaneEmbeddingData_of_admitsFaceBoundaryRunGeometry
    {G : SimpleGraph V}
    (hG : AdmitsFaceBoundaryRunGeometry G) :
    AdmitsOrderedFaceBoundaryPlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, ⟨geom.toOrderedFaceBoundaryData⟩⟩

theorem admitsOrderedFaceBoundaryPlaneEmbeddingData_iff_admitsFaceBoundaryRunGeometry
    {G : SimpleGraph V} :
    AdmitsOrderedFaceBoundaryPlaneEmbeddingData G ↔ AdmitsFaceBoundaryRunGeometry G := by
  constructor
  · exact admitsFaceBoundaryRunGeometry_of_admitsOrderedFaceBoundaryPlaneEmbeddingData
  · exact admitsOrderedFaceBoundaryPlaneEmbeddingData_of_admitsFaceBoundaryRunGeometry

theorem admitsOrderedFaceBoundaryVertexPlaneEmbeddingData_iff_admitsOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V} :
    AdmitsOrderedFaceBoundaryVertexPlaneEmbeddingData G ↔
      AdmitsOrderedFaceBoundaryPlaneEmbeddingData G := by
  constructor
  · exact admitsOrderedFaceBoundaryPlaneEmbeddingData_of_admitsOrderedFaceBoundaryVertexPlaneEmbeddingData
  · exact admitsOrderedFaceBoundaryVertexPlaneEmbeddingData_of_admitsOrderedFaceBoundaryPlaneEmbeddingData

theorem admitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_iff_admitsOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V} :
    AdmitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData G ↔
      AdmitsOrderedFaceBoundaryPlaneEmbeddingData G := by
  constructor
  ·
    exact
      admitsOrderedFaceBoundaryPlaneEmbeddingData_of_admitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData
  ·
    exact
      admitsOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_of_admitsOrderedFaceBoundaryPlaneEmbeddingData

theorem admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_iff_admitsFaceBoundaryClosedRunGeometry
    {G : SimpleGraph V} :
    AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G ↔ AdmitsFaceBoundaryClosedRunGeometry G := by
  constructor
  · exact admitsFaceBoundaryClosedRunGeometry_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
  · exact admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsFaceBoundaryClosedRunGeometry

theorem
    admitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData_iff_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V} :
    AdmitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData G ↔
      AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G := by
  constructor
  ·
    exact
      admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData
  ·
    exact
      admitsCyclicOrderedFaceBoundaryVertexPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData

theorem
    admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_iff_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V} :
    AdmitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData G ↔
      AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G := by
  constructor
  ·
    exact
      admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData
  ·
    exact
      admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_of_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData

theorem
    admitsFaceBoundaryClosedVertexWalkGeometry_iff_admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData
    {G : SimpleGraph V} :
    AdmitsFaceBoundaryClosedVertexWalkGeometry G ↔
      AdmitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData G := by
  constructor
  ·
    exact
      admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_of_admitsFaceBoundaryClosedVertexWalkGeometry
  ·
    exact
      admitsFaceBoundaryClosedVertexWalkGeometry_of_admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData

theorem admitsFaceBoundaryClosedVertexWalkGeometry_iff_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData
    {G : SimpleGraph V} :
    AdmitsFaceBoundaryClosedVertexWalkGeometry G ↔
      AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G := by
  rw
    [admitsFaceBoundaryClosedVertexWalkGeometry_iff_admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData,
      admitsCyclicOrderedFaceBoundaryVertexSequencePlaneEmbeddingData_iff_admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData]

theorem admitsFaceBoundaryClosedVertexWalkGeometry_iff_admitsFaceBoundaryClosedRunGeometry
    {G : SimpleGraph V} :
    AdmitsFaceBoundaryClosedVertexWalkGeometry G ↔ AdmitsFaceBoundaryClosedRunGeometry G := by
  constructor
  · exact admitsFaceBoundaryClosedRunGeometry_of_admitsFaceBoundaryClosedVertexWalkGeometry
  · exact admitsFaceBoundaryClosedVertexWalkGeometry_of_admitsFaceBoundaryClosedRunGeometry

end Mettapedia.GraphTheory
