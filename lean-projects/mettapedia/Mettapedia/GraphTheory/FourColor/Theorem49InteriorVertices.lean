import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryProjection
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryOuterBoundaryRootInteriorDual

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Purify a finite vertex set by deleting every vertex incident to the erased boundary support.
This is the concrete finite version of the interior-vertex side condition needed when boundary
projection is used in the Theorem 4.9 target. -/
noncomputable def verticesAvoidingEdgeSupport {G : SimpleGraph V}
    (boundary : Finset G.edgeSet) (vertices : Finset V) : Finset V := by
  classical
  exact vertices.filter fun v => ∀ e ∈ boundary, v ∉ (e : Sym2 V)

theorem mem_verticesAvoidingEdgeSupport_iff {G : SimpleGraph V}
    (boundary : Finset G.edgeSet) (vertices : Finset V) {v : V} :
    v ∈ verticesAvoidingEdgeSupport boundary vertices ↔
      v ∈ vertices ∧ ∀ e ∈ boundary, v ∉ (e : Sym2 V) := by
  classical
  simp [verticesAvoidingEdgeSupport]

theorem verticesAvoidingEdgeSupport_subset {G : SimpleGraph V}
    (boundary : Finset G.edgeSet) (vertices : Finset V) :
    verticesAvoidingEdgeSupport boundary vertices ⊆ vertices := by
  intro v hv
  exact (mem_verticesAvoidingEdgeSupport_iff boundary vertices).1 hv |>.1

theorem verticesAvoidingEdgeSupport_avoids {G : SimpleGraph V}
    (boundary : Finset G.edgeSet) (vertices : Finset V) :
    ∀ v ∈ verticesAvoidingEdgeSupport boundary vertices,
      ∀ e ∈ boundary, v ∉ (e : Sym2 V) := by
  intro v hv
  exact (mem_verticesAvoidingEdgeSupport_iff boundary vertices).1 hv |>.2

/-- Exact obstruction to using an unpurified vertex set: purification is the identity precisely when
the original finite vertex set already avoids the erased boundary support. -/
theorem verticesAvoidingEdgeSupport_eq_self_iff {G : SimpleGraph V}
    (boundary : Finset G.edgeSet) (vertices : Finset V) :
    verticesAvoidingEdgeSupport boundary vertices = vertices ↔
      ∀ v ∈ vertices, ∀ e ∈ boundary, v ∉ (e : Sym2 V) := by
  constructor
  · intro h v hv e he hve
    have hv' : v ∈ verticesAvoidingEdgeSupport boundary vertices := by
      simpa [h] using hv
    exact (mem_verticesAvoidingEdgeSupport_iff boundary vertices).1 hv' |>.2 e he hve
  · intro h
    ext v
    constructor
    · intro hv
      exact (mem_verticesAvoidingEdgeSupport_iff boundary vertices).1 hv |>.1
    · intro hv
      exact (mem_verticesAvoidingEdgeSupport_iff boundary vertices).2 ⟨hv, h v hv⟩

omit [DecidableEq V] in
theorem not_boundary_avoids_vertices_of_incident_boundary_edge {G : SimpleGraph V}
    {boundary : Finset G.edgeSet} {vertices : Finset V} {v : V} {e : G.edgeSet}
    (hv : v ∈ vertices) (he : e ∈ boundary) (hve : v ∈ (e : Sym2 V)) :
    ¬ (∀ v ∈ vertices, ∀ e ∈ boundary, v ∉ (e : Sym2 V)) := by
  intro h
  exact h v hv e he hve

theorem not_mem_verticesAvoidingEdgeSupport_of_incident_boundary_edge {G : SimpleGraph V}
    {boundary : Finset G.edgeSet} {vertices : Finset V} {v : V} {e : G.edgeSet}
    (he : e ∈ boundary) (hve : v ∈ (e : Sym2 V)) :
    v ∉ verticesAvoidingEdgeSupport boundary vertices := by
  intro hv
  exact (mem_verticesAvoidingEdgeSupport_iff boundary vertices).1 hv |>.2 e he hve

/-- The canonical finite interior-vertex purification relative to the selected outer boundary of a
boundary-aware embedding.  The ambient finite set is supplied by the caller, since the current
embedding interface does not yet package a global finite vertex set. -/
noncomputable def selectedBoundaryInteriorVertices {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V) : Finset V :=
  verticesAvoidingEdgeSupport
    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) vertices

theorem mem_selectedBoundaryInteriorVertices_iff {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V) {v : V} :
    v ∈ selectedBoundaryInteriorVertices emb vertices ↔
      v ∈ vertices ∧
        ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
          v ∉ (e : Sym2 V) :=
  mem_verticesAvoidingEdgeSupport_iff
    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) vertices

theorem selectedBoundaryInteriorVertices_subset {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V) :
    selectedBoundaryInteriorVertices emb vertices ⊆ vertices :=
  verticesAvoidingEdgeSupport_subset
    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) vertices

theorem selectedBoundaryInteriorVertices_avoids_selectedBoundarySupport {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V) :
    ∀ v ∈ selectedBoundaryInteriorVertices emb vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
        v ∉ (e : Sym2 V) :=
  verticesAvoidingEdgeSupport_avoids
    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) vertices

theorem selectedBoundaryInteriorVertices_eq_self_iff_selectedBoundary_avoids_vertices
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V) :
    selectedBoundaryInteriorVertices emb vertices = vertices ↔
      ∀ v ∈ vertices,
        ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
          v ∉ (e : Sym2 V) :=
  verticesAvoidingEdgeSupport_eq_self_iff
    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) vertices

/-- The finite set of primal endpoints touched by a finite set of graph edges. -/
def edgeEndpointSupport {G : SimpleGraph V} (edges : Finset G.edgeSet) : Finset V :=
  edges.biUnion fun e => (e : Sym2 V).toFinset

theorem mem_edgeEndpointSupport_iff {G : SimpleGraph V}
    (edges : Finset G.edgeSet) {v : V} :
    v ∈ edgeEndpointSupport edges ↔ ∃ e ∈ edges, v ∈ (e : Sym2 V) := by
  classical
  simp [edgeEndpointSupport, Sym2.mem_toFinset]

theorem edgeEndpointSupport_nonempty_of_nonempty {G : SimpleGraph V}
    {edges : Finset G.edgeSet} (hEdges : edges.Nonempty) :
    (edgeEndpointSupport edges).Nonempty := by
  classical
  rcases hEdges with ⟨e, he⟩
  rcases Sym2.mk_surjective (e : Sym2 V) with ⟨⟨x, y⟩, hxy⟩
  refine ⟨x, (mem_edgeEndpointSupport_iff edges).2 ⟨e, he, ?_⟩⟩
  simpa [hxy] using Sym2.mem_mk_left x y

theorem edgeEndpointSupport_disjoint_iff_no_shared_endpoint {G : SimpleGraph V}
    (left right : Finset G.edgeSet) :
    Disjoint (edgeEndpointSupport left) (edgeEndpointSupport right) ↔
      ∀ v,
        (∃ e ∈ left, v ∈ (e : Sym2 V)) →
          ∀ e ∈ right, v ∉ (e : Sym2 V) := by
  rw [Finset.disjoint_left]
  constructor
  · intro h v hv e he hve
    exact h ((mem_edgeEndpointSupport_iff left).2 hv)
      ((mem_edgeEndpointSupport_iff right).2 ⟨e, he, hve⟩)
  · intro h v hvLeft hvRight
    rcases (mem_edgeEndpointSupport_iff left).1 hvLeft with ⟨eLeft, heLeft, hvLeftEdge⟩
    rcases (mem_edgeEndpointSupport_iff right).1 hvRight with ⟨eRight, heRight, hvRightEdge⟩
    exact h v ⟨eLeft, heLeft, hvLeftEdge⟩ eRight heRight hvRightEdge

/-- The concrete finite vertex carrier available from a finite edge set: all vertices incident to
some graph edge.  This avoids requiring a global `Fintype V` instance and matches the edge-chain
surface used by the current Theorem 4.9 target. -/
def graphEdgeEndpointSupport (G : SimpleGraph V) [Fintype G.edgeSet] : Finset V :=
  edgeEndpointSupport (Finset.univ : Finset G.edgeSet)

theorem mem_graphEdgeEndpointSupport_iff {G : SimpleGraph V} [Fintype G.edgeSet] {v : V} :
    v ∈ graphEdgeEndpointSupport G ↔ ∃ e : G.edgeSet, v ∈ (e : Sym2 V) := by
  classical
  simp [graphEdgeEndpointSupport, mem_edgeEndpointSupport_iff]

theorem mem_graphEdgeEndpointSupport_of_mem_edge {G : SimpleGraph V} [Fintype G.edgeSet]
    {e : G.edgeSet} {v : V} (hv : v ∈ (e : Sym2 V)) :
    v ∈ graphEdgeEndpointSupport G :=
  (mem_graphEdgeEndpointSupport_iff (G := G)).2 ⟨e, hv⟩

/-- The canonical finite graph-interior vertex carrier for the current boundary-erasure route:
start from every vertex incident to a graph edge, then delete selected-boundary endpoints. -/
noncomputable def selectedBoundaryGraphInteriorVertices {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) : Finset V :=
  selectedBoundaryInteriorVertices emb (graphEdgeEndpointSupport G)

theorem mem_selectedBoundaryGraphInteriorVertices_iff {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) {v : V} :
    v ∈ selectedBoundaryGraphInteriorVertices emb ↔
      (∃ e : G.edgeSet, v ∈ (e : Sym2 V)) ∧
        ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
          v ∉ (e : Sym2 V) := by
  rw [selectedBoundaryGraphInteriorVertices,
    mem_selectedBoundaryInteriorVertices_iff,
    mem_graphEdgeEndpointSupport_iff]

theorem selectedBoundaryGraphInteriorVertices_avoids_selectedBoundarySupport
    {G : SimpleGraph V} [Fintype G.edgeSet] (emb : PlaneEmbeddingWithBoundary G) :
    ∀ v ∈ selectedBoundaryGraphInteriorVertices emb,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
        v ∉ (e : Sym2 V) :=
  selectedBoundaryInteriorVertices_avoids_selectedBoundarySupport emb (graphEdgeEndpointSupport G)

theorem not_mem_selectedBoundaryGraphInteriorVertices_of_incident_selectedBoundary
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {v : V} {e : G.edgeSet}
    (he : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hve : v ∈ (e : Sym2 V)) :
    v ∉ selectedBoundaryGraphInteriorVertices emb := by
  rw [selectedBoundaryGraphInteriorVertices]
  exact not_mem_verticesAvoidingEdgeSupport_of_incident_boundary_edge he hve

/-- Endpoints of the face-incidence interior edges of the current boundary-aware embedding.  This
is closer to the manuscript's annular interior-vertex language than the all-graph-edge endpoint
carrier: it starts from edges incident to two ambient faces, then a separate purification step
removes selected-boundary endpoints. -/
def interiorEdgeEndpointSupport {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Finset V :=
  edgeEndpointSupport (interiorEdgeSupport emb.faceBoundary emb.faces)

theorem mem_interiorEdgeEndpointSupport_iff {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) {v : V} :
    v ∈ interiorEdgeEndpointSupport emb ↔
      ∃ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces, v ∈ (e : Sym2 V) :=
  mem_edgeEndpointSupport_iff (interiorEdgeSupport emb.faceBoundary emb.faces)

theorem interiorEdgeEndpointSupport_nonempty_of_interiorEdgeSupport_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    (interiorEdgeEndpointSupport emb).Nonempty := by
  simpa [interiorEdgeEndpointSupport] using
    (edgeEndpointSupport_nonempty_of_nonempty
      (G := G) (edges := interiorEdgeSupport emb.faceBoundary emb.faces) hInterior)

/-- The interior-edge endpoint carrier after deleting endpoints incident to the selected ambient
boundary support. -/
noncomputable def selectedBoundaryInteriorEdgeEndpointVertices {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Finset V :=
  selectedBoundaryInteriorVertices emb (interiorEdgeEndpointSupport emb)

theorem mem_selectedBoundaryInteriorEdgeEndpointVertices_iff {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) {v : V} :
    v ∈ selectedBoundaryInteriorEdgeEndpointVertices emb ↔
      (∃ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces, v ∈ (e : Sym2 V)) ∧
        ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
          v ∉ (e : Sym2 V) := by
  rw [selectedBoundaryInteriorEdgeEndpointVertices,
    mem_selectedBoundaryInteriorVertices_iff,
    mem_interiorEdgeEndpointSupport_iff]

/-- A local endpoint witness for surviving selected-boundary purification: one endpoint of one
interior face-incidence edge is untouched by every selected ambient-boundary edge. -/
def HasUnblockedInteriorEndpoint {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ e, e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
    ∃ v, v ∈ (e : Sym2 V) ∧
      ∀ b ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
        v ∉ (b : Sym2 V)

/-- Exact witness form for nonempty purified interior-edge endpoint carriers.  A carrier survives
boundary erasure precisely when some endpoint of some interior face-incidence edge is not incident
to any selected ambient-boundary edge. -/
theorem selectedBoundaryInteriorEdgeEndpointVertices_nonempty_iff_exists_unblocked_interior_endpoint
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ↔
      ∃ e, e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
        ∃ v, v ∈ (e : Sym2 V) ∧
          ∀ b ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
            v ∉ (b : Sym2 V) := by
  constructor
  · rintro ⟨v, hv⟩
    rcases (mem_selectedBoundaryInteriorEdgeEndpointVertices_iff emb).1 hv with
      ⟨hInterior, hAvoid⟩
    rcases hInterior with ⟨e, heInterior, hvEdge⟩
    exact ⟨e, heInterior, v, hvEdge, hAvoid⟩
  · rintro ⟨e, heInterior, v, hvEdge, hAvoid⟩
    exact ⟨v, (mem_selectedBoundaryInteriorEdgeEndpointVertices_iff emb).2
      ⟨⟨e, heInterior, hvEdge⟩, hAvoid⟩⟩

/-- Named predicate form of the exact carrier nonemptiness criterion. -/
theorem hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    HasUnblockedInteriorEndpoint emb ↔
      (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  rw [HasUnblockedInteriorEndpoint]
  exact (selectedBoundaryInteriorEdgeEndpointVertices_nonempty_iff_exists_unblocked_interior_endpoint
    emb).symm

/-- A local unblocked endpoint witness contains an actual live interior face-incidence edge. -/
theorem interiorEdgeSupport_nonempty_of_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty := by
  rcases hEndpoint with ⟨e, heInterior, _v, _hv, _hAvoid⟩
  exact ⟨e, heInterior⟩

/-- Endpoint-support disjointness turns any raw interior-edge endpoint into a local unblocked
endpoint.  This is the bridge from the older endpoint-separation route surface to the named
constructive carrier witness. -/
theorem hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    HasUnblockedInteriorEndpoint emb := by
  rcases hRawCarrier with ⟨v, hvRaw⟩
  rcases (mem_interiorEdgeEndpointSupport_iff emb).1 hvRaw with
    ⟨e, heInterior, hvEdge⟩
  refine ⟨e, heInterior, v, hvEdge, ?_⟩
  intro b hb hvBoundaryEdge
  have hvBoundary : v ∈ edgeEndpointSupport
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :=
    (mem_edgeEndpointSupport_iff
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).2
      ⟨b, hb, hvBoundaryEdge⟩
  exact (Finset.disjoint_left.mp hEndpointDisjoint) hvRaw hvBoundary

/-- Graph-level endpoint-separation witness form for constructing a local unblocked endpoint. -/
theorem exists_hasUnblockedInteriorEndpoint_of_exists_endpointSupport_disjoint_and_nonempty
    {G : SimpleGraph V}
    (h : ∃ emb : PlaneEmbeddingWithBoundary G,
      Disjoint (interiorEdgeEndpointSupport emb)
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        (interiorEdgeEndpointSupport emb).Nonempty) :
    ∃ emb : PlaneEmbeddingWithBoundary G, HasUnblockedInteriorEndpoint emb := by
  rcases h with ⟨emb, hEndpointDisjoint, hRawCarrier⟩
  exact ⟨emb,
    hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
      hEndpointDisjoint hRawCarrier⟩

theorem selectedBoundaryInteriorEdgeEndpointVertices_subset_interiorEdgeEndpointSupport
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    selectedBoundaryInteriorEdgeEndpointVertices emb ⊆ interiorEdgeEndpointSupport emb :=
  selectedBoundaryInteriorVertices_subset emb (interiorEdgeEndpointSupport emb)

theorem selectedBoundaryInteriorEdgeEndpointVertices_avoids_selectedBoundarySupport
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    ∀ v ∈ selectedBoundaryInteriorEdgeEndpointVertices emb,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
        v ∉ (e : Sym2 V) :=
  selectedBoundaryInteriorVertices_avoids_selectedBoundarySupport emb
    (interiorEdgeEndpointSupport emb)

/-- Exact criterion for when the raw interior-edge endpoint carrier already satisfies the
boundary-erasure vertex side condition.  Edge-level disjointness of boundary and interior supports
is not enough; this is the required endpoint-level condition. -/
theorem selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_iff_no_endpoint_shared
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    selectedBoundaryInteriorEdgeEndpointVertices emb = interiorEdgeEndpointSupport emb ↔
      ∀ v,
        (∃ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces, v ∈ (e : Sym2 V)) →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
            v ∉ (e : Sym2 V) := by
  rw [selectedBoundaryInteriorEdgeEndpointVertices,
    selectedBoundaryInteriorVertices_eq_self_iff_selectedBoundary_avoids_vertices]
  constructor
  · intro h v hv e he hve
    exact h v ((mem_interiorEdgeEndpointSupport_iff emb).2 hv) e he hve
  · intro h v hv e he hve
    exact h v ((mem_interiorEdgeEndpointSupport_iff emb).1 hv) e he hve

/-- The missing geometric hypothesis in finite endpoint-support form.  This is the precise
strengthening over edge-set disjointness needed to use the raw interior-edge endpoint carrier. -/
theorem selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_iff_endpointSupport_disjoint
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) :
    selectedBoundaryInteriorEdgeEndpointVertices emb = interiorEdgeEndpointSupport emb ↔
      Disjoint (interiorEdgeEndpointSupport emb)
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) := by
  rw [selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_iff_no_endpoint_shared]
  change
    (∀ v,
        (∃ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces, v ∈ (e : Sym2 V)) →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
            v ∉ (e : Sym2 V)) ↔
      Disjoint (edgeEndpointSupport (interiorEdgeSupport emb.faceBoundary emb.faces))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
  exact
    (edgeEndpointSupport_disjoint_iff_no_shared_endpoint
      (interiorEdgeSupport emb.faceBoundary emb.faces)
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).symm

/-- Checked obstruction to using raw interior-edge endpoints without purification: if an interior
edge and a selected-boundary edge share a primal endpoint, the raw interior-edge endpoint carrier
cannot already be the purified carrier. -/
theorem selectedBoundaryInteriorEdgeEndpointVertices_ne_interiorEdgeEndpointSupport_of_endpoint_shared
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {v : V} {eInterior eBoundary : G.edgeSet}
    (heInterior : eInterior ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (heBoundary : eBoundary ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hvInterior : v ∈ (eInterior : Sym2 V))
    (hvBoundary : v ∈ (eBoundary : Sym2 V)) :
    selectedBoundaryInteriorEdgeEndpointVertices emb ≠ interiorEdgeEndpointSupport emb := by
  intro h
  have hnoEndpoint :=
    (selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_iff_no_endpoint_shared
      emb).1 h
  exact hnoEndpoint v ⟨eInterior, heInterior, hvInterior⟩ eBoundary heBoundary hvBoundary

/-- Endpoint-level separation is exactly the geometric hypothesis needed to use the raw
interior-edge endpoint carrier in the boundary-erasure route. -/
theorem interiorEdgeEndpointSupport_avoids_selectedBoundarySupport_of_no_endpoint_shared
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G)
    (hNoEndpoint :
      ∀ v,
        (∃ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces, v ∈ (e : Sym2 V)) →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
            v ∉ (e : Sym2 V)) :
    ∀ v ∈ interiorEdgeEndpointSupport emb,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
        v ∉ (e : Sym2 V) := by
  intro v hv
  exact hNoEndpoint v ((mem_interiorEdgeEndpointSupport_iff emb).1 hv)

/-- Boundary-erasure image form of the `W₀(H)` target with the interior-vertex side condition
discharged by selected-boundary purification.  This is the route-facing version of the
line-309 side condition: after purification, boundary projection preserves exactly the Kirchhoff
equations used in the target. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_eq_map_boundaryZeroProjection_kirchhoffSubmodule
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb (selectedBoundaryInteriorVertices emb vertices) =
      Submodule.map
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
        (kirchhoffSubmodule G (selectedBoundaryInteriorVertices emb vertices)) :=
  theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kirchhoffSubmodule_of_selectedBoundary_avoids_vertices
    (G := G) (emb := emb) (vertices := selectedBoundaryInteriorVertices emb vertices)
    (selectedBoundaryInteriorVertices_avoids_selectedBoundarySupport emb vertices)

/-- Graph-level boundary-erasure image form after selected-boundary interior-vertex purification. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_eq_map_boundaryZeroProjection_kirchhoffSubmodule_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorVertices emb (verticesOf emb data)) =
          Submodule.map
            (boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
            (kirchhoffSubmodule G
              (selectedBoundaryInteriorVertices emb (verticesOf emb data))) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_eq_map_boundaryZeroProjection_kirchhoffSubmodule
      (G := G) emb (verticesOf emb data)⟩

/-- The pointwise `W₀(H)` separation endpoint with the interior-vertex side condition discharged by
the selected-boundary purification of the supplied finite vertex set. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    (vertices : Finset V)
    {z : theorem49BoundaryZeroKirchhoffSubspace emb
      (selectedBoundaryInteriorVertices emb vertices)} :
    (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
      z = 0 :=
  theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
    (vertices := selectedBoundaryInteriorVertices emb vertices)
    (selectedBoundaryInteriorVertices_avoids_selectedBoundarySupport emb vertices)

/-- Graph-level form of the purified interior-vertex discharge: once the annulus/interior-dual route
data exists, the `W₀(H)` separation theorem applies to the selected-boundary interior purification
of any supplied finite vertex set. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorVertices emb (verticesOf emb data)),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun z =>
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (verticesOf emb data) (z := z)⟩

/-- Annulus-route form of the purified interior-vertex bridge.  From the outer-boundary-rooted
Step 2 data, selected-boundary purification simultaneously discharges the boundary-erasure image
identity for `W₀(H)` and the pointwise separation endpoint used in Theorem 4.9. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb (selectedBoundaryInteriorVertices emb vertices) =
        Submodule.map
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
          (kirchhoffSubmodule G (selectedBoundaryInteriorVertices emb vertices)) ∧
      ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorVertices emb vertices),
        (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
          z = 0 := by
  constructor
  · exact
      theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_eq_map_boundaryZeroProjection_kirchhoffSubmodule
        (G := G) emb vertices
  · intro z
    exact
      theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        (G := G) (emb := emb) (data := data.interiorData) (C₀ := C₀) (hC₀ := hC₀)
        vertices (z := z)

/-- Graph-level annulus-route form of the purified interior-vertex bridge. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_image_and_separation_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorVertices emb (verticesOf emb data)) =
            Submodule.map
              (boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
              (kirchhoffSubmodule G
                (selectedBoundaryInteriorVertices emb (verticesOf emb data))) ∧
          ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorVertices emb (verticesOf emb data)),
            (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
              z = 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀ (verticesOf emb data)⟩

/-- Annulus-route form with the face-incidence interior-edge endpoint carrier.  This is the
current closest formal proxy to the manuscript's annular interior vertices: start from endpoints of
edges incident to two ambient faces, then remove selected-boundary endpoints before applying the
boundary-erasure and separation endpoints. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) =
        Submodule.map
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
          (kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) ∧
      ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb),
        (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
          z = 0 :=
  theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    (G := G) data C₀ hC₀ (interiorEdgeEndpointSupport emb)

/-- Graph-level annulus-route endpoint with the face-incidence interior-edge endpoint carrier. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_image_and_separation_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb) =
            Submodule.map
              (boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
              (kirchhoffSubmodule G
                (selectedBoundaryInteriorEdgeEndpointVertices emb)) ∧
          ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb),
            (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
              z = 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Kernel-zero form of the purified interior-edge endpoint route.  The selected-boundary
purified carrier gives a concrete pairing map from `W₀(H)` into the dual of the projected
Definition 4.8 generator span, and the current outer-boundary-rooted annulus data makes that
pairing injective. -/
theorem
    ker_theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap_selectedBoundaryInteriorEdgeEndpointVertices_eq_bot_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    LinearMap.ker
        (theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
          (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb)) =
      ⊥ :=
  ker_theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap_eq_bot_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) (emb := emb) (data := data.interiorData) (C₀ := C₀) (hC₀ := hC₀)
    (vertices := selectedBoundaryInteriorEdgeEndpointVertices emb)
    (selectedBoundaryInteriorEdgeEndpointVertices_avoids_selectedBoundarySupport emb)

/-- Graph-level kernel-zero form for the selected-boundary purified interior-edge endpoint
carrier. -/
theorem
    exists_ker_theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap_selectedBoundaryInteriorEdgeEndpointVertices_eq_bot_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        LinearMap.ker
            (theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
              (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb)) =
          ⊥ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    ker_theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap_selectedBoundaryInteriorEdgeEndpointVertices_eq_bot_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Finite-dimensional consequence of the purified interior-edge endpoint route: the concrete
`W₀(H)` target over the selected-boundary purified carrier has dimension at most the projected
Definition 4.8 generator span. -/
theorem
    finrank_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_le_finrank_projectedKempeClosureGeneratorSubspace_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Module.finrank F2
        (theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb)) ≤
      Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀) :=
  finrank_theorem49BoundaryZeroKirchhoffSubspace_le_finrank_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) (emb := emb) (data := data.interiorData) (C₀ := C₀) (hC₀ := hC₀)
    (vertices := selectedBoundaryInteriorEdgeEndpointVertices emb)
    (selectedBoundaryInteriorEdgeEndpointVertices_avoids_selectedBoundarySupport emb)

/-- Graph-level finite-dimensional bound for the selected-boundary purified interior-edge endpoint
carrier. -/
theorem
    exists_finrank_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_le_finrank_projectedKempeClosureGeneratorSubspace_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        Module.finrank F2
            (theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb)) ≤
          Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    finrank_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_le_finrank_projectedKempeClosureGeneratorSubspace_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Concrete submodule characterization for the selected-boundary purified interior-edge endpoint
carrier: under the outer-boundary-rooted annulus route data, the `W₀(H)` target is exactly the
Kirchhoff equations at the purified carrier cut down by the projected Definition 4.8 generator
span. -/
theorem
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) =
      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
        projectedKempeClosureGeneratorSubspace emb C₀ :=
  theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) emb data.interiorData C₀ hC₀
    (selectedBoundaryInteriorEdgeEndpointVertices emb)

/-- Explicit projected-generator-family form of the purified interior-edge endpoint target
characterization. -/
theorem
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_eq_kirchhoffSubmodule_inf_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) =
      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
        Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) :=
  theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) emb data.interiorData C₀ hC₀
    (selectedBoundaryInteriorEdgeEndpointVertices emb)

/-- Direct inclusion form of the purified interior-edge endpoint route: every chain in the
selected-boundary purified `W₀(H)` target lies in the projected Definition 4.8 generator span. -/
theorem
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_le_projectedKempeClosureGeneratorSubspace_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) ≤
      projectedKempeClosureGeneratorSubspace emb C₀ :=
  theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) emb data.interiorData C₀ hC₀
    (selectedBoundaryInteriorEdgeEndpointVertices emb)

/-- Explicit-family inclusion form of the purified interior-edge endpoint route. -/
theorem
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_le_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) ≤
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) :=
  theorem49BoundaryZeroKirchhoffSubspace_le_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) emb data.interiorData C₀ hC₀
    (selectedBoundaryInteriorEdgeEndpointVertices emb)

/-- Graph-level submodule characterization for the selected-boundary purified interior-edge
endpoint carrier. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb) =
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
            projectedKempeClosureGeneratorSubspace emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level direct inclusion form for the selected-boundary purified interior-edge endpoint
carrier. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_le_projectedKempeClosureGeneratorSubspace_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb) ≤
          projectedKempeClosureGeneratorSubspace emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_le_projectedKempeClosureGeneratorSubspace_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Operational projected-generator form of the purified route: every selected-boundary purified
interior-edge endpoint `W₀(H)` chain is a finite linear combination of projected Definition 4.8
generators. -/
theorem
    exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆
          projectedKempeClosureGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z :=
  exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) emb data.interiorData C₀ hC₀
    (selectedBoundaryInteriorEdgeEndpointVertices emb) hz

/-- Operational raw-generator form of the purified route: every selected-boundary purified
interior-edge endpoint `W₀(H)` chain is the selected-boundary projection of a finite raw
Definition 4.8 generator combination, and the raw sum already satisfies the Kirchhoff equations at
the purified carrier. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_and_mem_kirchhoffSubmodule_of_mem_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆
          kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈
              kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
            boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (∑ y ∈ terms, coeff y • y) = z :=
  exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_and_mem_kirchhoffSubmodule_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) emb data.interiorData C₀ hC₀
    (selectedBoundaryInteriorEdgeEndpointVertices emb)
    (selectedBoundaryInteriorEdgeEndpointVertices_avoids_selectedBoundarySupport emb) hz

/-- Graph-level operational projected-generator form for the selected-boundary purified
interior-edge endpoint carrier. -/
theorem
    exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  projectedKempeClosureGeneratorFamily emb C₀ ∧
                coeff.support ⊆ terms ∧
                  ∑ y ∈ terms, coeff y • y = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hz

/-- Graph-level operational raw-generator form for the selected-boundary purified interior-edge
endpoint carrier. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_and_mem_kirchhoffSubmodule_of_mem_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  (∑ y ∈ terms, coeff y • y) ∈
                      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                    boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                        (∑ y ∈ terms, coeff y • y) = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_and_mem_kirchhoffSubmodule_of_mem_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hz

/-- Corrected raw-source image form for the selected-boundary purified interior-edge endpoint
carrier: the concrete target is the selected-boundary erasure of raw Definition 4.8 generator-span
chains that are already Kirchhoff at the purified carrier. -/
theorem
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) =
      Submodule.map
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
        (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :=
  theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) emb data.interiorData C₀ hC₀
    (selectedBoundaryInteriorEdgeEndpointVertices emb)
    (selectedBoundaryInteriorEdgeEndpointVertices_avoids_selectedBoundarySupport emb)

/-- Raw-source preimage form for the selected-boundary purified interior-edge endpoint carrier. -/
theorem
    exists_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
        kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb),
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z :=
  exists_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) emb data.interiorData C₀ hC₀
    (selectedBoundaryInteriorEdgeEndpointVertices emb)
    (selectedBoundaryInteriorEdgeEndpointVertices_avoids_selectedBoundarySupport emb) hz

/-- Raw Kirchhoff representative form for the purified carrier: any raw Kirchhoff chain has the
same selected-boundary-erased image as a finite raw Definition 4.8 generator sum that remains
Kirchhoff at the purified carrier. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_eq_boundaryZeroProjection_of_mem_kirchhoffSubmodule_selectedBoundaryInteriorEdgeEndpointVertices_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆
          kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈
              kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
            boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (∑ y ∈ terms, coeff y • y) =
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x :=
  exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_eq_boundaryZeroProjection_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) emb data.interiorData C₀ hC₀
    (selectedBoundaryInteriorEdgeEndpointVertices emb)
    (selectedBoundaryInteriorEdgeEndpointVertices_avoids_selectedBoundarySupport emb) hx

/-- Boundary-kernel decomposition form for the purified carrier: any raw Kirchhoff chain is a raw
Definition 4.8 generator sum plus an error that is both Kirchhoff at the purified carrier and
supported on the selected-boundary coordinates. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryKernel_error_decomposition_of_mem_kirchhoffSubmodule_selectedBoundaryInteriorEdgeEndpointVertices_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (boundaryError : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆
          kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈
              kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
            boundaryError ∈
                kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
                  LinearMap.ker
                    (boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
              (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                    (∑ y ∈ terms, coeff y • y) =
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x :=
  exists_kempeClosureGeneratorFamily_finset_sum_boundaryKernel_error_decomposition_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) emb data.interiorData C₀ hC₀
    (selectedBoundaryInteriorEdgeEndpointVertices emb)
    (selectedBoundaryInteriorEdgeEndpointVertices_avoids_selectedBoundarySupport emb) hx

/-- Graph-level corrected raw-source image form for the selected-boundary purified interior-edge
endpoint carrier. -/
theorem
    exists_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb) =
          Submodule.map
            (boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
            (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level raw-source preimage form for the selected-boundary purified interior-edge endpoint
carrier. -/
theorem
    exists_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb),
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hz

/-- Graph-level boundary-kernel decomposition form for raw Kirchhoff chains at the
selected-boundary purified interior-edge endpoint carrier. -/
theorem
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryKernel_error_decomposition_of_mem_kirchhoffSubmodule_selectedBoundaryInteriorEdgeEndpointVertices_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        ∀ {x : G.edgeSet → Color},
          x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
                (boundaryError : G.edgeSet → Color),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  (∑ y ∈ terms, coeff y • y) ∈
                      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                    boundaryError ∈
                        kirchhoffSubmodule G
                            (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
                          LinearMap.ker
                            (boundaryZeroProjection
                              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
                      (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                        boundaryZeroProjection
                          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                            (∑ y ∈ terms, coeff y • y) =
                          boundaryZeroProjection
                            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro x hx
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryKernel_error_decomposition_of_mem_kirchhoffSubmodule_selectedBoundaryInteriorEdgeEndpointVertices_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hx

/-- Annulus-route form for the raw face-incidence interior-edge endpoint carrier, conditional on
the endpoint-level separation that the current annulus data does not yet prove.  This is the
precise theorem needed if the manuscript's intended interior vertices are taken to be raw endpoints
of interior annulus edges rather than the selected-boundary purification. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hNoEndpoint :
      ∀ v,
        (∃ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces, v ∈ (e : Sym2 V)) →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
            v ∉ (e : Sym2 V)) :
    theorem49BoundaryZeroKirchhoffSubspace emb (interiorEdgeEndpointSupport emb) =
        Submodule.map
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
          (kirchhoffSubmodule G (interiorEdgeEndpointSupport emb)) ∧
      ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
          (interiorEdgeEndpointSupport emb),
        (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
          z = 0 := by
  have hboundary :
      ∀ v ∈ interiorEdgeEndpointSupport emb,
        ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
          v ∉ (e : Sym2 V) :=
    interiorEdgeEndpointSupport_avoids_selectedBoundarySupport_of_no_endpoint_shared
      emb hNoEndpoint
  constructor
  · exact
      theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kirchhoffSubmodule_of_selectedBoundary_avoids_vertices
        (G := G) (emb := emb) (vertices := interiorEdgeEndpointSupport emb) hboundary
  · intro z
    exact
      theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        (G := G) (emb := emb) (data := data.interiorData) (C₀ := C₀) (hC₀ := hC₀)
        (vertices := interiorEdgeEndpointSupport emb) hboundary (z := z)

/-- Same raw-carrier annulus route, with the missing geometry stated as finite endpoint-support
disjointness. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_endpointSupport_disjoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hEndpointDisjoint :
      Disjoint (interiorEdgeEndpointSupport emb)
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    theorem49BoundaryZeroKirchhoffSubspace emb (interiorEdgeEndpointSupport emb) =
        Submodule.map
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
          (kirchhoffSubmodule G (interiorEdgeEndpointSupport emb)) ∧
      ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
          (interiorEdgeEndpointSupport emb),
        (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
          z = 0 := by
  have hNoEndpoint :
      ∀ v,
        (∃ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces, v ∈ (e : Sym2 V)) →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
            v ∉ (e : Sym2 V) := by
    exact
      (edgeEndpointSupport_disjoint_iff_no_shared_endpoint
        (interiorEdgeSupport emb.faceBoundary emb.faces)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).1
        (by simpa [interiorEdgeEndpointSupport] using hEndpointDisjoint)
  exact
    theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hNoEndpoint

/-- Graph-level raw interior-edge endpoint route, parameterized by the missing endpoint-level
geometric separation proof. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hNoEndpointOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb →
        ∀ v,
          (∃ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces, v ∈ (e : Sym2 V)) →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
              v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (interiorEdgeEndpointSupport emb) =
            Submodule.map
              (boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
              (kirchhoffSubmodule G (interiorEdgeEndpointSupport emb)) ∧
          ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
              (interiorEdgeEndpointSupport emb),
            (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
              z = 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀ (hNoEndpointOf emb data)⟩

/-- Graph-level raw interior-edge endpoint route with endpoint-support disjointness as the
geometric input. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_of_endpointSupport_disjoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hEndpointDisjointOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb →
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (interiorEdgeEndpointSupport emb) =
            Submodule.map
              (boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
              (kirchhoffSubmodule G (interiorEdgeEndpointSupport emb)) ∧
          ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
              (interiorEdgeEndpointSupport emb),
            (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
              z = 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_endpointSupport_disjoint
      (G := G) data C₀ hC₀ (hEndpointDisjointOf emb data)⟩

/-- Outer-boundary-rooted annulus route data equipped with the exact endpoint-level separation
needed to use the unpurified raw interior-edge endpoint carrier.  The diamond obstruction shows
that this field is not a consequence of facial closed-walk data alone. -/
structure PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) where
  routeData : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb
  hEndpointDisjoint :
    Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))

/-- Graph-level existence of outer-boundary-rooted annulus route data together with the endpoint
separation needed for the raw interior-edge endpoint carrier. -/
def AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty
      (PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation emb)

/-- Raw interior-edge endpoint route from annulus data that already contains the endpoint
separation/no-touch obligation. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data :
      PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    theorem49BoundaryZeroKirchhoffSubspace emb (interiorEdgeEndpointSupport emb) =
        Submodule.map
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
          (kirchhoffSubmodule G (interiorEdgeEndpointSupport emb)) ∧
      ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
          (interiorEdgeEndpointSupport emb),
        (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
          z = 0 :=
  theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_endpointSupport_disjoint
    (G := G) data.routeData C₀ hC₀ data.hEndpointDisjoint

/-- Graph-level raw interior-edge endpoint route from annulus data that explicitly includes the
missing endpoint-separation/no-touch field. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG :
      AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data :
        PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (interiorEdgeEndpointSupport emb) =
            Submodule.map
              (boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
              (kirchhoffSubmodule G (interiorEdgeEndpointSupport emb)) ∧
          ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
              (interiorEdgeEndpointSupport emb),
            (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
              z = 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_interiorEdgeEndpointSupport_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
      (G := G) data C₀ hC₀⟩

/-- The packaged endpoint-separation route data makes selected-boundary purification lossless on
the raw interior-edge endpoint carrier. This is the exact finite-support repair needed to turn the
current purified Theorem 4.9 endpoint into a non-vacuous raw-carrier endpoint once the raw carrier
is known to be nonempty. -/
theorem
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation.selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation emb) :
    selectedBoundaryInteriorEdgeEndpointVertices emb = interiorEdgeEndpointSupport emb :=
  (selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_iff_endpointSupport_disjoint
    emb).2 data.hEndpointDisjoint

/-- Annulus-route form with the concrete graph-edge endpoint carrier.  This is the current
formal replacement for an unspecified interior-vertex set: all endpoints of graph edges are
available from `[Fintype G.edgeSet]`, and selected-boundary purification removes exactly the
vertices where boundary erasure could change a Kirchhoff equation. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryGraphInteriorVertices_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    theorem49BoundaryZeroKirchhoffSubspace emb (selectedBoundaryGraphInteriorVertices emb) =
        Submodule.map
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
          (kirchhoffSubmodule G (selectedBoundaryGraphInteriorVertices emb)) ∧
      ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryGraphInteriorVertices emb),
        (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
          z = 0 :=
  theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    (G := G) data C₀ hC₀ (graphEdgeEndpointSupport G)

/-- Graph-level annulus-route endpoint with the concrete graph-edge endpoint carrier. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryGraphInteriorVertices_image_and_separation_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryGraphInteriorVertices emb) =
            Submodule.map
              (boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
              (kirchhoffSubmodule G (selectedBoundaryGraphInteriorVertices emb)) ∧
          ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryGraphInteriorVertices emb),
            (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
              z = 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryGraphInteriorVertices_image_and_separation_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

end Mettapedia.GraphTheory.FourColor
