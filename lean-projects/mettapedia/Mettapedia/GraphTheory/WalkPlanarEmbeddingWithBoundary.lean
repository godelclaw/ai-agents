import Mettapedia.GraphTheory.OrderedPlanarEmbeddingWithBoundary
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walks.Traversal

namespace Mettapedia.GraphTheory

universe u

variable {V : Type u} [DecidableEq V]

/-- A bundled walk-based strengthening of `PlaneEmbeddingWithBoundary`: every embedded face is
witnessed by an actual nonempty closed simple walk whose traversed edges lie exactly on that face
boundary. This is the stronger source interface needed for the boundary-order blocker, before any
later lowering into ordered edge/vertex boundary lists. -/
structure PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  faceBoundaryClosedWalk :
    ∀ f : {f // f ∈ emb.faces}, PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f

namespace PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk

variable {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {f : {f // f ∈ emb.faces}}

private def boundaryDartEdge (d : G.Dart) : G.edgeSet :=
  ⟨d.edge, d.edge_mem⟩

/-- The actual ordered boundary-edge list induced by the facial walk. -/
def boundaryEdgeRun (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) : List G.edgeSet :=
  data.walk.darts.map boundaryDartEdge

/-- The ordered list of terminal vertices of the facial walk darts. The entry at each position is
the vertex shared by that dart's edge and the cyclic successor edge. -/
def boundaryVertexRun (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) : List V :=
  data.walk.darts.map fun d => d.snd

theorem edge_mem_faceBoundary_image
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f)
    {e : Sym2 V} (he : e ∈ data.walk.edges) :
    e ∈ (emb.faceBoundary f.1).image Subtype.val :=
  data.hedge_sub e he

theorem faceBoundary_edge_mem_walk
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f)
    {e : G.edgeSet} (he : e ∈ emb.faceBoundary f.1) :
    (e : Sym2 V) ∈ data.walk.edges :=
  data.hface_sub e he

theorem walk_edges_nodup
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    data.walk.edges.Nodup :=
  data.hnodup_edges

theorem walk_length_pos
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    0 < data.walk.length :=
  data.hnonempty

theorem walk_not_nil
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    ¬ data.walk.Nil :=
  (SimpleGraph.Walk.not_nil_iff_lt_length).2 data.walk_length_pos

theorem boundaryEdgeRun_map_val
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    data.boundaryEdgeRun.map Subtype.val = data.walk.edges := by
  simp [boundaryEdgeRun, SimpleGraph.Walk.edges, boundaryDartEdge]

theorem mem_boundaryEdgeRun_iff_mem_walk
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f)
    {e : G.edgeSet} :
    e ∈ data.boundaryEdgeRun ↔ (e : Sym2 V) ∈ data.walk.edges := by
  constructor
  · intro he
    rw [← data.boundaryEdgeRun_map_val]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  · intro he
    rw [SimpleGraph.Walk.edges] at he
    rcases List.mem_map.mp he with ⟨d, hd, hde⟩
    exact List.mem_map.mpr ⟨d, hd, Subtype.ext hde⟩

theorem edge_mem_faceBoundary_image_iff
    {e : G.edgeSet} :
    (e : Sym2 V) ∈ (emb.faceBoundary f.1).image Subtype.val ↔ e ∈ emb.faceBoundary f.1 := by
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨e', he', hEq⟩
    cases Subtype.ext hEq
    exact he'
  · intro he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩

theorem mem_boundaryEdgeRun_iff
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f)
    {e : G.edgeSet} :
    e ∈ data.boundaryEdgeRun ↔ e ∈ emb.faceBoundary f.1 := by
  constructor
  · intro he
    exact (edge_mem_faceBoundary_image_iff (emb := emb) (f := f) (e := e)).1 <|
      data.edge_mem_faceBoundary_image ((data.mem_boundaryEdgeRun_iff_mem_walk (e := e)).1 he)
  · intro he
    exact (data.mem_boundaryEdgeRun_iff_mem_walk (e := e)).2 <|
      data.faceBoundary_edge_mem_walk he

/-- A face with an honest nonempty boundary walk has a nonempty face-boundary edge set. -/
theorem faceBoundary_nonempty
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    (emb.faceBoundary f.1).Nonempty := by
  have hlen : 0 < data.walk.edges.length := by
    simpa [SimpleGraph.Walk.length_edges] using data.hnonempty
  cases hcases : data.walk.edges with
  | nil =>
      simp [hcases] at hlen
  | cons e es =>
      have he : e ∈ data.walk.edges := by
        rw [hcases]
        simp
      obtain ⟨e', he', _⟩ := Finset.mem_image.mp (data.edge_mem_faceBoundary_image he)
      exact ⟨e', he'⟩

omit [DecidableEq V] in
private theorem closedTrail_three_le_length {G : SimpleGraph V} {u : V}
    {p : G.Walk u u} (hnonempty : 0 < p.length) (hnodup : p.edges.Nodup) :
    3 ≤ p.length := by
  match p with
  | .nil => simp at hnonempty
  | .cons h .nil => simp at h
  | .cons _ (.cons _ .nil) =>
      simp at hnodup
  | .cons _ (.cons _ (.cons _ _)) =>
      simp

theorem boundaryEdgeRun_nodup
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    data.boundaryEdgeRun.Nodup := by
  apply (List.nodup_map_iff (f := (Subtype.val : G.edgeSet → Sym2 V)) Subtype.val_injective).1
  simpa [data.boundaryEdgeRun_map_val] using data.walk_edges_nodup

/-- An honest nonempty simple closed facial walk in a simple graph uses at least three boundary
edges.  This rules out singleton terminal peeled faces at the closed-walk source layer. -/
theorem three_le_faceBoundary_card
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    3 ≤ (emb.faceBoundary f.1).card := by
  have hlen3 : 3 ≤ data.walk.length :=
    closedTrail_three_le_length data.hnonempty data.hnodup_edges
  have hset : data.boundaryEdgeRun.toFinset = emb.faceBoundary f.1 := by
    ext e
    simp [PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk.mem_boundaryEdgeRun_iff]
  have hcard_eq_run : (emb.faceBoundary f.1).card = data.boundaryEdgeRun.length := by
    rw [← hset]
    exact List.toFinset_card_of_nodup data.boundaryEdgeRun_nodup
  have hrun_len : data.boundaryEdgeRun.length = data.walk.length := by
    have h := congrArg List.length data.boundaryEdgeRun_map_val
    simpa [SimpleGraph.Walk.length_edges] using h
  rw [hcard_eq_run, hrun_len]
  exact hlen3

theorem boundaryVertexRun_length_eq_boundaryEdgeRun_length
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    data.boundaryVertexRun.length = data.boundaryEdgeRun.length := by
  simp [boundaryVertexRun, boundaryEdgeRun]

theorem boundaryVertexRun_incident_here
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    List.Forall₂ (fun v (e : G.edgeSet) => v ∈ (e : Sym2 V))
      data.boundaryVertexRun data.boundaryEdgeRun := by
  change List.Forall₂ (fun v (e : G.edgeSet) => v ∈ (e : Sym2 V))
    (data.walk.darts.map fun d => d.snd)
    (data.walk.darts.map boundaryDartEdge)
  induction data.walk.darts with
  | nil =>
      exact .nil
  | cons d ds ih =>
      refine .cons ?_ ih
      change d.snd ∈ d.edge
      simpa [SimpleGraph.Dart.edge] using Sym2.mem_mk_right d.fst d.snd

private theorem boundaryDartRun_closed
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    List.IsChain G.DartAdj (data.walk.darts ++ data.walk.darts.head?.toList) := by
  have hnil := data.walk_not_nil
  have hdartsNil : data.walk.darts ≠ [] := by
    simpa [SimpleGraph.Walk.darts_eq_nil] using hnil
  have hfirst :
      data.walk.darts.head? = some (data.walk.firstDart hnil) := by
    rw [List.head?_eq_some_head hdartsNil, data.walk.firstDart_eq_head_darts hnil]
  have hlast :
      data.walk.darts.getLast? = some (data.walk.lastDart hnil) := by
    rw [List.getLast?_eq_getLast_of_ne_nil hdartsNil,
      data.walk.getLast_darts_eq_lastDart hdartsNil]
  have hheadChain : List.IsChain G.DartAdj data.walk.darts.head?.toList := by
    simp [hfirst]
  refine data.walk.isChain_dartAdj_darts.append hheadChain ?_
  intro x hx y hy
  have hx' : data.walk.lastDart hnil = x := by
    simpa [hlast, Option.mem_def] using hx
  have hy' : data.walk.firstDart hnil = y := by
    simpa [hfirst, Option.mem_def] using hy
  subst x
  subst y
  simp [SimpleGraph.DartAdj]

omit [DecidableEq V] in
private theorem forall₂_snd_mem_boundaryDartEdge_of_forall₂_dartAdj
    {G : SimpleGraph V} {as bs : List G.Dart}
    (h : List.Forall₂ G.DartAdj as bs) :
    List.Forall₂ (fun v (e : G.edgeSet) => v ∈ (e : Sym2 V))
      (as.map fun d => d.snd) (bs.map boundaryDartEdge) := by
  induction h with
  | nil =>
      exact .nil
  | @cons d₁ d₂ _ _ hAdj _ ih =>
      refine .cons ?_ ih
      change d₁.snd ∈ d₂.edge
      have hfst : d₁.snd = d₂.fst := by
        simpa [SimpleGraph.DartAdj] using hAdj
      rw [hfst]
      simpa [SimpleGraph.Dart.edge] using Sym2.mem_mk_left d₂.fst d₂.snd

omit [DecidableEq V] in
private theorem forall₂_dart_snd_mem_next_boundaryDartEdge_rotate
    {G : SimpleGraph V} {ds : List G.Dart}
    (hclosed : List.IsChain G.DartAdj (ds ++ ds.head?.toList)) :
    List.Forall₂ (fun v (e : G.edgeSet) => v ∈ (e : Sym2 V))
      (ds.map fun d => d.snd) ((ds.map boundaryDartEdge).rotate 1) := by
  cases ds with
  | nil =>
      simp
  | cons d ds =>
      have hclosed' : List.IsChain G.DartAdj (d :: ds ++ [d]) := by
        simpa using hclosed
      have hpair : List.Forall₂ G.DartAdj (d :: ds) (ds ++ [d]) := by
        exact List.isChain_cons_append_singleton_iff_forall₂.1 hclosed'
      have hmem :=
        forall₂_snd_mem_boundaryDartEdge_of_forall₂_dartAdj hpair
      rw [show ((d :: ds).map boundaryDartEdge).rotate 1 =
          (ds ++ [d]).map boundaryDartEdge by simp [List.map_append]]
      exact hmem

theorem boundaryVertexRun_incident_next
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    List.Forall₂ (fun v (e : G.edgeSet) => v ∈ (e : Sym2 V))
      data.boundaryVertexRun (data.boundaryEdgeRun.rotate 1) := by
  simpa [boundaryVertexRun, boundaryEdgeRun, List.map_rotate]
    using
      forall₂_dart_snd_mem_next_boundaryDartEdge_rotate
        (boundaryDartRun_closed data)

omit [DecidableEq V] in
private theorem forall₂_edgeSet_incidence_to_sym2
    {G : SimpleGraph V} {vs : List V} {es : List G.edgeSet}
    (h : List.Forall₂ (fun v (e : G.edgeSet) => v ∈ (e : Sym2 V)) vs es) :
    List.Forall₂ (fun v (e : Sym2 V) => v ∈ e) vs es.unattach := by
  induction h with
  | nil =>
      simp
  | @cons v e vs es hve _ ih =>
      simpa using
        (@List.Forall₂.cons V (Sym2 V) (fun v (e : Sym2 V) => v ∈ e)
          v (e : Sym2 V) vs es.unattach hve ih)

theorem boundaryVertexRun_incident_here_sym2
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    List.Forall₂ (fun v (e : Sym2 V) => v ∈ e)
      data.boundaryVertexRun data.boundaryEdgeRun.unattach :=
  forall₂_edgeSet_incidence_to_sym2 data.boundaryVertexRun_incident_here

theorem boundaryVertexRun_incident_next_sym2
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    List.Forall₂ (fun v (e : Sym2 V) => v ∈ e)
      data.boundaryVertexRun (data.boundaryEdgeRun.rotate 1).unattach :=
  forall₂_edgeSet_incidence_to_sym2 data.boundaryVertexRun_incident_next

omit [DecidableEq V] in
private theorem walk_supportTail_forall₂_edges
    {G : SimpleGraph V} {u v : V} :
    ∀ (p : G.Walk u v), List.Forall₂ (fun (x : V) (e : Sym2 V) => x ∈ e) p.support.tail p.edges
  | .nil =>
      .nil
  | @SimpleGraph.Walk.cons _ _ u v w h p =>
      by
        have hmem : v ∈ s(u, v) := by
          simp [Sym2.mem_iff]
        rw [SimpleGraph.Walk.support_cons, List.tail_cons, SimpleGraph.Walk.edges_cons, p.support_eq_cons]
        exact
          @List.Forall₂.cons V (Sym2 V) (fun (x : V) (e : Sym2 V) => x ∈ e)
            v (s(u, v)) p.support.tail p.edges hmem (walk_supportTail_forall₂_edges p)

private theorem boundaryAdj_of_darts
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f)
    {d d' : G.Dart}
    (hd : d ∈ data.walk.darts) (hd' : d' ∈ data.walk.darts)
    (hAdj : G.DartAdj d d') :
    planarEmbeddingBoundaryEdgeEndpointAdj (boundaryDartEdge d) (boundaryDartEdge d') := by
  refine ⟨?_, ⟨d.snd, ?_, ?_⟩⟩
  · intro hEq
    rcases List.getElem_of_mem hd with ⟨i, hi, hdi⟩
    rcases List.getElem_of_mem hd' with ⟨j, hj, hdj⟩
    have hi' : i < data.walk.edges.length := by
      simpa [SimpleGraph.Walk.length_darts] using hi
    have hj' : j < data.walk.edges.length := by
      simpa [SimpleGraph.Walk.length_darts] using hj
    have hEdgesEq : data.walk.edges[i]'hi' = data.walk.edges[j]'hj' := by
      simpa [SimpleGraph.Walk.edges, hdi, hdj, boundaryDartEdge, hi', hj'] using
        congrArg Subtype.val hEq
    have hij' : i = j := by
      exact (List.Nodup.getElem_inj_iff data.walk_edges_nodup (hi := hi') (hj := hj')).1 hEdgesEq
    subst hij'
    have hdd' : d = d' := hdi.symm.trans hdj
    have hAdj' := hAdj
    simp [hdd', SimpleGraph.DartAdj] at hAdj'
  · change d.snd ∈ d.edge
    simpa [SimpleGraph.Dart.edge] using Sym2.mem_mk_right d.fst d.snd
  · change d.snd ∈ d'.edge
    have hAdj' : d.snd = d'.fst := by simpa [SimpleGraph.DartAdj] using hAdj
    exact hAdj' ▸ (by simpa [SimpleGraph.Dart.edge] using Sym2.mem_mk_left d'.fst d'.snd)

theorem boundaryEdgeRun_chain
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj data.boundaryEdgeRun := by
  have hdartChain :
      List.IsChain
        (fun d d' : G.Dart =>
          planarEmbeddingBoundaryEdgeEndpointAdj (boundaryDartEdge d) (boundaryDartEdge d'))
        data.walk.darts := by
    refine (data.walk.isChain_dartAdj_darts).imp_of_mem_tail_imp ?_
    intro d d' hd hd' hAdj
    exact boundaryAdj_of_darts data hd (List.mem_of_mem_tail hd') hAdj
  simpa [boundaryEdgeRun, boundaryDartEdge] using
    (List.isChain_map_of_isChain boundaryDartEdge (fun _ _ h => h) hdartChain)

theorem boundaryEdgeRun_closed
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj
      (data.boundaryEdgeRun ++ data.boundaryEdgeRun.head?.toList) := by
  have hnil := data.walk_not_nil
  have hdartsNil : data.walk.darts ≠ [] := by
    simpa [SimpleGraph.Walk.darts_eq_nil] using hnil
  have hfirst :
      data.boundaryEdgeRun.head? = some (boundaryDartEdge (data.walk.firstDart hnil)) := by
    rw [boundaryEdgeRun, List.head?_map, List.head?_eq_some_head hdartsNil,
      data.walk.firstDart_eq_head_darts hnil]
    rfl
  have hlast :
      data.boundaryEdgeRun.getLast? = some (boundaryDartEdge (data.walk.lastDart hnil)) := by
    rw [boundaryEdgeRun, List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil hdartsNil,
      data.walk.getLast_darts_eq_lastDart hdartsNil]
    rfl
  have hheadChain :
      List.IsChain planarEmbeddingBoundaryEdgeEndpointAdj data.boundaryEdgeRun.head?.toList := by
    simp [hfirst]
  refine (data.boundaryEdgeRun_chain).append
    hheadChain ?_
  intro x hx y hy
  have hx' : boundaryDartEdge (data.walk.lastDart hnil) = x := by
    simpa [hlast, Option.mem_def] using hx
  have hy' : boundaryDartEdge (data.walk.firstDart hnil) = y := by
    simpa [hfirst, Option.mem_def] using hy
  subst x
  subst y
  exact boundaryAdj_of_darts data
    (data.walk.lastDart_mem_darts hnil) (data.walk.firstDart_mem_darts hnil)
    (by simp [SimpleGraph.DartAdj])

/-- One honest facial walk lowers directly to the existing closed boundary-run shell. -/
def toFaceBoundaryClosedEndpointRun
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedEndpointRun emb f where
  run := data.boundaryEdgeRun
  hclosed := data.boundaryEdgeRun_closed
  hnodup := data.boundaryEdgeRun_nodup
  hmem := fun e => data.mem_boundaryEdgeRun_iff (e := e)

/-- One honest facial walk lowers directly to the cyclic edge/vertex boundary-walk shell, using
the actual dart terminal vertices as the cyclic shared endpoints. -/
def toFaceBoundaryClosedVertexWalk
    (data : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk emb f) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalk emb f where
  toFaceBoundaryClosedEndpointRun := data.toFaceBoundaryClosedEndpointRun
  vertices := data.boundaryVertexRun
  hincident_here := by
    simpa [toFaceBoundaryClosedEndpointRun] using data.boundaryVertexRun_incident_here_sym2
  hincident_next := by
    simpa [toFaceBoundaryClosedEndpointRun] using data.boundaryVertexRun_incident_next_sym2

end PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalk

namespace PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry

variable {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}

/-- Bundled honest facial walks lower directly to the existing bundled closed boundary-run
geometry package. -/
def toFaceBoundaryClosedRunGeometry
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry emb where
  faceBoundaryClosedRun := fun f =>
    (geom.faceBoundaryClosedWalk f).toFaceBoundaryClosedEndpointRun

/-- The bundled honest facial walk layer also yields cyclic ordered face-boundary data by first
passing through the closed boundary-run package already used downstream. -/
def toCyclicOrderedFaceBoundaryData
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) :
    PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb :=
  geom.toFaceBoundaryClosedRunGeometry.toCyclicOrderedFaceBoundaryData

/-- Honest facial walks lower all the way to the bundled explicit cyclic edge/vertex boundary-walk
geometry already used by the FourColor route, retaining the concrete shared vertices from the
walk darts. -/
def toFaceBoundaryClosedVertexWalkGeometry
    (geom : PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) :
    PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry emb where
  faceBoundaryClosedVertexWalk := fun f =>
    (geom.faceBoundaryClosedWalk f).toFaceBoundaryClosedVertexWalk

end PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry

/-- Graph-level existence form of the stronger actual-walk boundary interface. -/
def AdmitsFaceBoundaryClosedWalkGeometry (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb)

/-- On a fixed embedding, honest facial walks yield the bundled cyclic boundary-run shell. -/
theorem nonempty_faceBoundaryClosedWalkGeometry_implies_nonempty_faceBoundaryClosedRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) →
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry emb) := by
  rintro ⟨geom⟩
  exact ⟨geom.toFaceBoundaryClosedRunGeometry⟩

/-- On a fixed embedding, honest facial walks also yield cyclic ordered face-boundary data. -/
theorem nonempty_faceBoundaryClosedWalkGeometry_implies_nonempty_cyclicOrderedFaceBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) →
      Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData emb) := by
  rintro ⟨geom⟩
  exact ⟨geom.toCyclicOrderedFaceBoundaryData⟩

/-- On a fixed embedding, honest facial walks lower all the way to cyclic alternating
edge/vertex boundary-walk geometry. -/
theorem nonempty_faceBoundaryClosedWalkGeometry_implies_nonempty_faceBoundaryClosedVertexWalkGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) →
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry emb) := by
  rintro ⟨geom⟩
  exact ⟨geom.toFaceBoundaryClosedVertexWalkGeometry⟩

/-- Consequently, on a fixed embedding, honest facial walks also yield the linear face-boundary
run shell used by the selected-boundary-arc layer. -/
theorem nonempty_faceBoundaryClosedWalkGeometry_implies_nonempty_faceBoundaryRunGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry emb) →
      Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry emb) := by
  intro h
  exact
    (nonempty_orderedFaceBoundaryData_iff_nonempty_faceBoundaryRunGeometry).mp <|
      nonempty_cyclicOrderedFaceBoundaryData_implies_nonempty_orderedFaceBoundaryData <|
        nonempty_faceBoundaryClosedWalkGeometry_implies_nonempty_cyclicOrderedFaceBoundaryData h

/-- The honest face-walk source layer lowers graph-level existence directly to the bundled cyclic
boundary-run layer already used downstream. -/
theorem admitsFaceBoundaryClosedRunGeometry_of_admitsFaceBoundaryClosedWalkGeometry
    {G : SimpleGraph V} (hG : AdmitsFaceBoundaryClosedWalkGeometry G) :
    AdmitsFaceBoundaryClosedRunGeometry G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, ⟨geom.toFaceBoundaryClosedRunGeometry⟩⟩

/-- The honest face-walk source layer also yields graph-level cyclic ordered face-boundary data.
-/
theorem admitsCyclicOrderedFaceBoundaryPlaneEmbeddingData_of_admitsFaceBoundaryClosedWalkGeometry
    {G : SimpleGraph V} (hG : AdmitsFaceBoundaryClosedWalkGeometry G) :
    AdmitsCyclicOrderedFaceBoundaryPlaneEmbeddingData G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, ⟨geom.toCyclicOrderedFaceBoundaryData⟩⟩

/-- Honest facial walks lower graph-level existence all the way to the cyclic alternating
edge/vertex boundary-walk geometry used later in the FourColor route. -/
theorem admitsFaceBoundaryClosedVertexWalkGeometry_of_admitsFaceBoundaryClosedWalkGeometry
    {G : SimpleGraph V} (hG : AdmitsFaceBoundaryClosedWalkGeometry G) :
    AdmitsFaceBoundaryClosedVertexWalkGeometry G := by
  rcases hG with ⟨emb, ⟨geom⟩⟩
  exact ⟨emb, ⟨geom.toFaceBoundaryClosedVertexWalkGeometry⟩⟩

/-- Consequently the honest face-walk source layer also yields the linear face-boundary run shell
used by the selected-boundary-arc layer. -/
theorem admitsFaceBoundaryRunGeometry_of_admitsFaceBoundaryClosedWalkGeometry
    {G : SimpleGraph V} (hG : AdmitsFaceBoundaryClosedWalkGeometry G) :
    AdmitsFaceBoundaryRunGeometry G := by
  exact
    admitsFaceBoundaryRunGeometry_of_admitsFaceBoundaryClosedRunGeometry
      (admitsFaceBoundaryClosedRunGeometry_of_admitsFaceBoundaryClosedWalkGeometry hG)

end Mettapedia.GraphTheory
