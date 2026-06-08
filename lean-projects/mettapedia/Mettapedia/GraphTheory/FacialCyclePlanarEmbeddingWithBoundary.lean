import Mettapedia.GraphTheory.WalkPlanarEmbeddingWithBoundary
import Mathlib.Combinatorics.SimpleGraph.Walks.Operations

namespace Mettapedia.GraphTheory

universe u

variable {V : Type u} [DecidableEq V]

variable {G : SimpleGraph V}

/-- Endpoint of the walk obtained by following a nonempty list of darts whose first dart is `d`.
For `[]`, following `d` ends at `d.snd`; for a nonempty tail, the endpoint is the endpoint of the
tail's last dart. -/
private def dartListEnd (d : G.Dart) : List G.Dart → V
  | [] => d.snd
  | d' :: ds => dartListEnd d' ds

/-- Construct the open walk obtained by following a nonempty chained list of darts. -/
private def dartChainWalk (d : G.Dart) :
    (ds : List G.Dart) → List.IsChain G.DartAdj (d :: ds) →
      G.Walk d.fst (dartListEnd d ds)
  | [], _ => SimpleGraph.Walk.cons d.adj SimpleGraph.Walk.nil
  | d' :: ds, hchain =>
      have hAdj : G.DartAdj d d' :=
        (List.isChain_cons.mp hchain).1 d' (by simp)
      have htail : List.IsChain G.DartAdj (d' :: ds) :=
        (List.isChain_cons.mp hchain).2
      SimpleGraph.Walk.cons d.adj ((dartChainWalk d' ds htail).copy hAdj.symm rfl)

omit [DecidableEq V] in
/-- The open walk built from a chained dart list realizes exactly that dart list. -/
private theorem dartChainWalk_darts (d : G.Dart) :
    ∀ (ds : List G.Dart) (hchain : List.IsChain G.DartAdj (d :: ds)),
      (dartChainWalk d ds hchain).darts = d :: ds
  | [], _ => by
      simp [dartChainWalk]
  | d' :: ds, hchain => by
      have hAdj : G.DartAdj d d' :=
        (List.isChain_cons.mp hchain).1 d' (by simp)
      have htail : List.IsChain G.DartAdj (d' :: ds) :=
        (List.isChain_cons.mp hchain).2
      dsimp [dartChainWalk]
      rw [SimpleGraph.Walk.darts_copy, dartChainWalk_darts d' ds htail]

omit [DecidableEq V] in
/-- If a chained nonempty dart list is followed by a target dart, then the endpoint of the open
walk along that list is the first vertex of the target. -/
private theorem dartListEnd_eq_target_of_chain_append (d : G.Dart) :
    ∀ (ds : List G.Dart) (target : G.Dart),
      List.IsChain G.DartAdj ((d :: ds) ++ [target]) →
        dartListEnd d ds = target.fst
  | [], target, hchain => by
      have hAdj : G.DartAdj d target := by
        simpa using (List.isChain_pair.mp hchain)
      simpa [dartListEnd, SimpleGraph.DartAdj] using hAdj
  | d' :: ds, target, hchain => by
      have htail : List.IsChain G.DartAdj ((d' :: ds) ++ [target]) :=
        (List.isChain_cons.mp hchain).2
      exact dartListEnd_eq_target_of_chain_append d' ds target htail

omit [DecidableEq V] in
/-- A pure cyclic dart list determines a closed walk realizing exactly that list of darts. -/
theorem exists_closedWalk_darts_eq_of_isChain_dartAdj_append_head
    {darts : List G.Dart}
    (hnonempty : darts ≠ [])
    (hclosed : List.IsChain G.DartAdj (darts ++ darts.head?.toList)) :
    ∃ baseVertex : V, ∃ walk : G.Walk baseVertex baseVertex, walk.darts = darts := by
  cases hdarts : darts with
  | nil =>
      exact False.elim (hnonempty hdarts)
  | cons d ds =>
      have hclosed' : List.IsChain G.DartAdj ((d :: ds) ++ [d]) := by
        simpa [hdarts] using hclosed
      have hchain : List.IsChain G.DartAdj (d :: ds) :=
        List.IsChain.left_of_append (l₂ := [d]) hclosed'
      have hend : dartListEnd d ds = d.fst :=
        dartListEnd_eq_target_of_chain_append d ds d hclosed'
      refine ⟨d.fst, (dartChainWalk d ds hchain).copy rfl hend, ?_⟩
      simpa [SimpleGraph.Walk.darts_copy, hdarts] using dartChainWalk_darts d ds hchain

/-- A facial dart-cycle source for one embedded face.  The source supplies the ordered darts
around the face, proves that this dart list is cyclically adjacent, and records the actual
`SimpleGraph.Walk` realization whose darts are exactly that cycle.  This is the minimal
embedding-side strengthening needed before lowering to the older closed-walk interface: unordered
face-edge incidence alone is deliberately not used to infer the walk. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryDartCycle {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (f : {f // f ∈ emb.faces}) where
  /-- The base vertex of the realized closed walk. -/
  baseVertex : V
  /-- The Mathlib closed walk realizing the listed facial darts. -/
  walk : G.Walk baseVertex baseVertex
  /-- The cyclic list of darts around the face. -/
  darts : List G.Dart
  /-- The walk realizes exactly the supplied dart cycle. -/
  hdarts : walk.darts = darts
  /-- The facial dart cycle is nonempty. -/
  hnonempty : darts ≠ []
  /-- Consecutive darts, including the last-to-first pair, are walk-adjacent. -/
  hclosed : List.IsChain G.DartAdj (darts ++ darts.head?.toList)
  /-- The cycle traverses each unoriented boundary edge at most once. -/
  hnodup_edges : (darts.map fun d => d.edge).Nodup
  /-- Every traversed dart edge lies in this face boundary. -/
  hedge_sub : ∀ d ∈ darts, d.edge ∈ (emb.faceBoundary f.1).image Subtype.val
  /-- Every edge of this face boundary is traversed by the dart cycle. -/
  hface_sub : ∀ e ∈ emb.faceBoundary f.1, (e : Sym2 V) ∈ darts.map fun d => d.edge

/-- A pure facial dart-cycle source for one embedded face.  Unlike `FaceBoundaryDartCycle`, this
does not carry a walk as input: the walk is constructed mechanically from the nonempty cyclic
dart-adjacency proof. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (f : {f // f ∈ emb.faces}) where
  /-- The cyclic list of darts around the face. -/
  darts : List G.Dart
  /-- The facial dart cycle is nonempty. -/
  hnonempty : darts ≠ []
  /-- Consecutive darts, including the last-to-first pair, are walk-adjacent. -/
  hclosed : List.IsChain G.DartAdj (darts ++ darts.head?.toList)
  /-- The cycle traverses each unoriented boundary edge at most once. -/
  hnodup_edges : (darts.map fun d => d.edge).Nodup
  /-- Every traversed dart edge lies in this face boundary. -/
  hedge_sub : ∀ d ∈ darts, d.edge ∈ (emb.faceBoundary f.1).image Subtype.val
  /-- Every edge of this face boundary is traversed by the dart cycle. -/
  hface_sub : ∀ e ∈ emb.faceBoundary f.1, (e : Sym2 V) ∈ darts.map fun d => d.edge

/-- A successor-based facial dart-cycle source for one embedded face.  This is the small
rotation-side interface below `FaceBoundaryPureDartCycle`: it supplies a cyclic list of face darts
and an explicit successor function whose listed successor steps are dart-adjacent. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (f : {f // f ∈ emb.faces}) where
  /-- The cyclic list of darts around the face. -/
  darts : List G.Dart
  /-- The facial dart cycle is nonempty. -/
  hnonempty : darts ≠ []
  /-- The successor operation around this face.  Only its values on `darts` are constrained. -/
  successor : G.Dart → G.Dart
  /-- The list order is exactly the successor order, including the last-to-first step. -/
  hsuccessor_order :
    List.Forall₂ (fun d d' : G.Dart => successor d = d')
      darts (darts.tail ++ darts.head?.toList)
  /-- Each listed successor step is a valid walk-adjacent dart step. -/
  hsuccessor_adj : ∀ d ∈ darts, G.DartAdj d (successor d)
  /-- The cycle traverses each unoriented boundary edge at most once. -/
  hnodup_edges : (darts.map fun d => d.edge).Nodup
  /-- Every traversed dart edge lies in this face boundary. -/
  hedge_sub : ∀ d ∈ darts, d.edge ∈ (emb.faceBoundary f.1).image Subtype.val
  /-- Every edge of this face boundary is traversed by the dart cycle. -/
  hface_sub : ∀ e ∈ emb.faceBoundary f.1, (e : Sym2 V) ∈ darts.map fun d => d.edge

namespace PlaneEmbeddingWithBoundary.FaceBoundaryDartCycle

variable {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
  {f : {f // f ∈ emb.faces}}

/-- The realized walk has the same edge list as the supplied facial dart cycle. -/
theorem walk_edges_eq_dart_edges
    (cycle : PlaneEmbeddingWithBoundary.FaceBoundaryDartCycle emb f) :
    cycle.walk.edges = cycle.darts.map fun d => d.edge := by
  simp [SimpleGraph.Walk.edges, cycle.hdarts]

/-- A facial dart-cycle source lowers to the existing closed-walk source for the same embedded
face.  The proof is purely mechanical: the walk is already part of the source, while exactness of
the boundary support is transferred through `walk.darts = darts`. -/
def toFaceBoundaryClosedWalk
    (cycle : PlaneEmbeddingWithBoundary.FaceBoundaryDartCycle emb f) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f where
  baseVertex := cycle.baseVertex
  walk := cycle.walk
  hnonempty := by
    have hlenDarts : 0 < cycle.darts.length := by
      cases hd : cycle.darts with
      | nil => exact False.elim (cycle.hnonempty hd)
      | cons d ds => simp
    have hlenWalkDarts : 0 < cycle.walk.darts.length := by
      simpa [cycle.hdarts] using hlenDarts
    simpa [SimpleGraph.Walk.length_darts] using hlenWalkDarts
  hnodup_edges := by
    simpa [cycle.walk_edges_eq_dart_edges] using cycle.hnodup_edges
  hedge_sub := by
    intro e he
    rw [cycle.walk_edges_eq_dart_edges] at he
    rcases List.mem_map.mp he with ⟨d, hd, hde⟩
    simpa [hde] using cycle.hedge_sub d hd
  hface_sub := by
    intro e he
    simpa [cycle.walk_edges_eq_dart_edges] using cycle.hface_sub e he

end PlaneEmbeddingWithBoundary.FaceBoundaryDartCycle

namespace PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle

variable {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
  {f : {f // f ∈ emb.faces}}

/-- A pure facial dart cycle lowers to the realized dart-cycle source on the same face by
constructing the closed walk from cyclic dart adjacency. -/
def toFaceBoundaryDartCycle
    (cycle : PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle emb f) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartCycle emb f :=
  match hdarts : cycle.darts with
  | [] => False.elim (cycle.hnonempty hdarts)
  | d :: ds =>
      have hclosed' : List.IsChain G.DartAdj ((d :: ds) ++ [d]) := by
        simpa [hdarts] using cycle.hclosed
      have hchain : List.IsChain G.DartAdj (d :: ds) :=
        List.IsChain.left_of_append (l₂ := [d]) hclosed'
      have hend : dartListEnd d ds = d.fst :=
        dartListEnd_eq_target_of_chain_append d ds d hclosed'
      let walk : G.Walk d.fst d.fst := (dartChainWalk d ds hchain).copy rfl hend
      { baseVertex := d.fst
        walk := walk
        darts := cycle.darts
        hdarts := by
          show walk.darts = cycle.darts
          simpa [walk, SimpleGraph.Walk.darts_copy, hdarts] using
            dartChainWalk_darts d ds hchain
        hnonempty := cycle.hnonempty
        hclosed := cycle.hclosed
        hnodup_edges := cycle.hnodup_edges
        hedge_sub := cycle.hedge_sub
        hface_sub := cycle.hface_sub }

/-- A pure facial dart cycle also lowers directly to the closed facial-walk source. -/
def toFaceBoundaryClosedWalk
    (cycle : PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle emb f) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f :=
  cycle.toFaceBoundaryDartCycle.toFaceBoundaryClosedWalk

end PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle

namespace PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle

variable {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
  {f : {f // f ∈ emb.faces}}

omit [DecidableEq V] in
private theorem forall₂_dartAdj_of_successor_order
    (successor : G.Dart → G.Dart) :
    ∀ {as bs : List G.Dart},
      List.Forall₂ (fun d d' : G.Dart => successor d = d') as bs →
      (∀ d ∈ as, G.DartAdj d (successor d)) →
        List.Forall₂ G.DartAdj as bs
  | [], [], _, _ => .nil
  | a :: as, b :: bs, horder, hadj => by
      cases horder with
      | cons hab htail =>
          refine .cons ?_ ?_
          · rw [← hab]
            exact hadj a (by simp)
          · exact forall₂_dartAdj_of_successor_order successor htail
              (fun d hd => hadj d (by simp [hd]))

/-- The successor-based source lowers to a pure cyclic dart source by forgetting the successor
operation after using it to prove cyclic `DartAdj`. -/
def toFaceBoundaryPureDartCycle
    (cycle : PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle emb f) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle emb f where
  darts := cycle.darts
  hnonempty := cycle.hnonempty
  hclosed := by
    have hpairAll :
        List.Forall₂ G.DartAdj cycle.darts (cycle.darts.tail ++ cycle.darts.head?.toList) :=
      forall₂_dartAdj_of_successor_order cycle.successor
        cycle.hsuccessor_order cycle.hsuccessor_adj
    cases hdarts : cycle.darts with
    | nil =>
        exact False.elim (cycle.hnonempty hdarts)
    | cons d ds =>
        have hpair : List.Forall₂ G.DartAdj (d :: ds) (ds ++ [d]) := by
          simpa [hdarts] using hpairAll
        have hclosed' : List.IsChain G.DartAdj (d :: ds ++ [d]) :=
          List.isChain_cons_append_singleton_iff_forall₂.2 hpair
        simpa [hdarts] using hclosed'
  hnodup_edges := cycle.hnodup_edges
  hedge_sub := cycle.hedge_sub
  hface_sub := cycle.hface_sub

/-- The successor-based source lowers to a realized facial dart cycle. -/
def toFaceBoundaryDartCycle
    (cycle : PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle emb f) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartCycle emb f :=
  cycle.toFaceBoundaryPureDartCycle.toFaceBoundaryDartCycle

/-- The successor-based source lowers directly to the closed facial-walk source. -/
def toFaceBoundaryClosedWalk
    (cycle : PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle emb f) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f :=
  cycle.toFaceBoundaryPureDartCycle.toFaceBoundaryClosedWalk

end PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle

/-- Bundled facial dart-cycle source data: every embedded face has one realized cyclic dart list
whose unoriented edge support is exactly its face boundary. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryDartCycleGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  faceBoundaryDartCycle :
    ∀ f : {f // f ∈ emb.faces}, PlaneEmbeddingWithBoundary.FaceBoundaryDartCycle emb f

/-- Bundled pure facial dart-cycle source data: every embedded face has one cyclic dart list whose
unoriented edge support is exactly its face boundary; closed walks are constructed from the dart
cycle proofs rather than supplied as fields. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  faceBoundaryPureDartCycle :
    ∀ f : {f // f ∈ emb.faces}, PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle emb f

/-- Bundled successor-based facial dart-cycle source data: every embedded face has one local
successor operation on its cyclic dart list. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycleGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  faceBoundaryDartSuccessorCycle :
    ∀ f : {f // f ∈ emb.faces},
      PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle emb f

namespace PlaneEmbeddingWithBoundary.FaceBoundaryDartCycleGeometry

variable {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}

/-- Bundled facial dart cycles lower to bundled closed facial walks on the same embedding. -/
def toFaceBoundaryClosedWalkGeometry
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryDartCycleGeometry emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb where
  faceBoundaryClosedWalk := fun f =>
    (geom.faceBoundaryDartCycle f).toFaceBoundaryClosedWalk

end PlaneEmbeddingWithBoundary.FaceBoundaryDartCycleGeometry

namespace PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry

variable {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}

/-- Bundled pure facial dart cycles lower to bundled realized facial dart cycles. -/
def toFaceBoundaryDartCycleGeometry
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartCycleGeometry emb where
  faceBoundaryDartCycle := fun f =>
    (geom.faceBoundaryPureDartCycle f).toFaceBoundaryDartCycle

/-- Bundled pure facial dart cycles lower to bundled closed facial walks on the same embedding. -/
def toFaceBoundaryClosedWalkGeometry
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb :=
  geom.toFaceBoundaryDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

end PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry

namespace PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycleGeometry

variable {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}

/-- Bundled successor-based facial dart cycles lower to bundled pure facial dart cycles. -/
def toFaceBoundaryPureDartCycleGeometry
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycleGeometry emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry emb where
  faceBoundaryPureDartCycle := fun f =>
    (geom.faceBoundaryDartSuccessorCycle f).toFaceBoundaryPureDartCycle

/-- Bundled successor-based facial dart cycles lower to bundled realized facial dart cycles. -/
def toFaceBoundaryDartCycleGeometry
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycleGeometry emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartCycleGeometry emb :=
  geom.toFaceBoundaryPureDartCycleGeometry.toFaceBoundaryDartCycleGeometry

/-- Bundled successor-based facial dart cycles lower to bundled closed facial walks. -/
def toFaceBoundaryClosedWalkGeometry
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycleGeometry emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb :=
  geom.toFaceBoundaryPureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

end PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycleGeometry

/-- Graph-level existence form of the facial dart-cycle source. -/
def AdmitsFaceBoundaryDartCycleGeometry (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryDartCycleGeometry emb)

/-- Graph-level existence form of the pure facial dart-cycle source. -/
def AdmitsFaceBoundaryPureDartCycleGeometry (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry emb)

/-- Graph-level existence form of the successor-based facial dart-cycle source. -/
def AdmitsFaceBoundaryDartSuccessorCycleGeometry (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycleGeometry emb)

/-- On a fixed embedding, facial dart cycles yield the closed-walk source required downstream. -/
theorem nonempty_faceBoundaryDartCycleGeometry_implies_nonempty_faceBoundaryClosedWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryDartCycleGeometry emb) →
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) := by
  rintro ⟨geom⟩
  exact ⟨geom.toFaceBoundaryClosedWalkGeometry⟩

/-- On a fixed embedding, pure facial dart cycles yield realized facial dart cycles. -/
theorem nonempty_faceBoundaryPureDartCycleGeometry_implies_nonempty_faceBoundaryDartCycleGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry emb) →
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryDartCycleGeometry emb) := by
  rintro ⟨geom⟩
  exact ⟨geom.toFaceBoundaryDartCycleGeometry⟩

/-- On a fixed embedding, pure facial dart cycles yield the closed-walk source required
downstream. -/
theorem nonempty_faceBoundaryPureDartCycleGeometry_implies_nonempty_faceBoundaryClosedWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry emb) →
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) := by
  rintro ⟨geom⟩
  exact ⟨geom.toFaceBoundaryClosedWalkGeometry⟩

/-- On a fixed embedding, successor-based facial dart cycles yield pure facial dart cycles. -/
theorem
    nonempty_faceBoundaryDartSuccessorCycleGeometry_implies_nonempty_faceBoundaryPureDartCycleGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycleGeometry emb) →
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry emb) := by
  rintro ⟨geom⟩
  exact ⟨geom.toFaceBoundaryPureDartCycleGeometry⟩

/-- On a fixed embedding, successor-based facial dart cycles yield realized facial dart cycles. -/
theorem
    nonempty_faceBoundaryDartSuccessorCycleGeometry_implies_nonempty_faceBoundaryDartCycleGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycleGeometry emb) →
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryDartCycleGeometry emb) := by
  rintro ⟨geom⟩
  exact ⟨geom.toFaceBoundaryDartCycleGeometry⟩

/-- On a fixed embedding, successor-based facial dart cycles yield the closed-walk source. -/
theorem
    nonempty_faceBoundaryDartSuccessorCycleGeometry_implies_nonempty_faceBoundaryClosedWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycleGeometry emb) →
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) := by
  rintro ⟨geom⟩
  exact ⟨geom.toFaceBoundaryClosedWalkGeometry⟩

/-- Graph-level facial dart-cycle sources instantiate the existing graph-level closed-walk
embedding data. -/
theorem admitsFaceBoundaryClosedWalkGeometry_of_admitsFaceBoundaryDartCycleGeometry
    {G : SimpleGraph V} (hG : AdmitsFaceBoundaryDartCycleGeometry G) :
    AdmitsFaceBoundaryClosedWalkGeometry G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, ⟨geom.toFaceBoundaryClosedWalkGeometry⟩⟩

/-- Graph-level pure facial dart-cycle sources instantiate realized facial dart cycles. -/
theorem admitsFaceBoundaryDartCycleGeometry_of_admitsFaceBoundaryPureDartCycleGeometry
    {G : SimpleGraph V} (hG : AdmitsFaceBoundaryPureDartCycleGeometry G) :
    AdmitsFaceBoundaryDartCycleGeometry G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, ⟨geom.toFaceBoundaryDartCycleGeometry⟩⟩

/-- Graph-level pure facial dart-cycle sources instantiate the existing graph-level closed-walk
embedding data. -/
theorem admitsFaceBoundaryClosedWalkGeometry_of_admitsFaceBoundaryPureDartCycleGeometry
    {G : SimpleGraph V} (hG : AdmitsFaceBoundaryPureDartCycleGeometry G) :
    AdmitsFaceBoundaryClosedWalkGeometry G := by
  exact admitsFaceBoundaryClosedWalkGeometry_of_admitsFaceBoundaryDartCycleGeometry
    (admitsFaceBoundaryDartCycleGeometry_of_admitsFaceBoundaryPureDartCycleGeometry hG)

/-- Graph-level successor-based facial dart-cycle sources instantiate pure facial dart cycles. -/
theorem admitsFaceBoundaryPureDartCycleGeometry_of_admitsFaceBoundaryDartSuccessorCycleGeometry
    {G : SimpleGraph V} (hG : AdmitsFaceBoundaryDartSuccessorCycleGeometry G) :
    AdmitsFaceBoundaryPureDartCycleGeometry G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, ⟨geom.toFaceBoundaryPureDartCycleGeometry⟩⟩

/-- Graph-level successor-based facial dart-cycle sources instantiate realized facial dart
cycles. -/
theorem admitsFaceBoundaryDartCycleGeometry_of_admitsFaceBoundaryDartSuccessorCycleGeometry
    {G : SimpleGraph V} (hG : AdmitsFaceBoundaryDartSuccessorCycleGeometry G) :
    AdmitsFaceBoundaryDartCycleGeometry G := by
  exact admitsFaceBoundaryDartCycleGeometry_of_admitsFaceBoundaryPureDartCycleGeometry
    (admitsFaceBoundaryPureDartCycleGeometry_of_admitsFaceBoundaryDartSuccessorCycleGeometry hG)

/-- Graph-level successor-based facial dart-cycle sources instantiate the existing graph-level
closed-walk embedding data. -/
theorem admitsFaceBoundaryClosedWalkGeometry_of_admitsFaceBoundaryDartSuccessorCycleGeometry
    {G : SimpleGraph V} (hG : AdmitsFaceBoundaryDartSuccessorCycleGeometry G) :
    AdmitsFaceBoundaryClosedWalkGeometry G := by
  exact admitsFaceBoundaryClosedWalkGeometry_of_admitsFaceBoundaryPureDartCycleGeometry
    (admitsFaceBoundaryPureDartCycleGeometry_of_admitsFaceBoundaryDartSuccessorCycleGeometry hG)

end Mettapedia.GraphTheory
