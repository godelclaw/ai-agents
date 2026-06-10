import Mettapedia.GraphTheory.FourColor.PlanarBoundaryOrderedEmbedding
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.OrderedPlanarEmbeddingWithBoundaryRegression
import Mettapedia.GraphTheory.WalkPlanarEmbeddingWithBoundaryRegression

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open scoped Classical

noncomputable section

namespace PlanarBoundaryFaceBoundaryRunRegression

open Mettapedia.GraphTheory.OrderedPlanarEmbeddingWithBoundaryRegression
open Mettapedia.GraphTheory.WalkPlanarEmbeddingWithBoundaryRegression

def hs01 : e01 ∈ selectedBoundarySupport
    badEmbedding.faceBoundary badEmbedding.faces badEmbedding.faces := by
  simp [selectedBoundarySupport, totalIncidenceCount, badEmbedding, badFaces, badFaceBoundary, e01]

def hs23 : e23 ∈ selectedBoundarySupport
    badEmbedding.faceBoundary badEmbedding.faces badEmbedding.faces := by
  simp [selectedBoundarySupport, totalIncidenceCount, badEmbedding, badFaces, badFaceBoundary, e23]

def be01 : PlanarBoundaryEdgeVertex badEmbedding := ⟨e01, hs01⟩

def be23 : PlanarBoundaryEdgeVertex badEmbedding := ⟨e23, hs23⟩

theorem edgeVertex_eq_be01_or_be23 (x : PlanarBoundaryEdgeVertex badEmbedding) :
    x = be01 ∨ x = be23 := by
  rcases edge_eq_e01_or_e23 x.1 with h | h
  · left
    exact Subtype.ext h
  · right
    exact Subtype.ext h

theorem supportGraph_eq_bot :
    planarBoundarySupportEndpointAdjGraph badEmbedding = ⊥ := by
  ext x y
  constructor
  · intro hxy
    rcases edgeVertex_eq_be01_or_be23 x with rfl | rfl <;>
      rcases edgeVertex_eq_be01_or_be23 y with rfl | rfl <;>
      simp [be01, be23, planarBoundarySupportEndpointAdjGraph, e01, e23, badGraph] at hxy
  · intro hxy
    simp at hxy

theorem not_reachable_be01_be23 :
    ¬ (planarBoundarySupportEndpointAdjGraph badEmbedding).Reachable be01 be23 := by
  intro hreach
  have hreachBot : (⊥ : SimpleGraph (PlanarBoundaryEdgeVertex badEmbedding)).Reachable be01 be23 := by
    simpa [supportGraph_eq_bot] using hreach
  have hEq : be01 = be23 := (SimpleGraph.reachable_bot).1 hreachBot
  exact e01_ne_e23 (congrArg Subtype.val hEq)

theorem mem_selectedBoundarySupport_iff_mem_onlyFaceBoundary {e : badGraph.edgeSet} :
    e ∈ selectedBoundarySupport badEmbedding.faceBoundary badEmbedding.faces badEmbedding.faces ↔
      e ∈ badEmbedding.faceBoundary onlyFace.1 := by
  rcases edge_eq_e01_or_e23 e with rfl | rfl <;>
    simp [selectedBoundarySupport, totalIncidenceCount, badEmbedding, badFaces, badFaceBoundary,
      onlyFace, e01, e23]

/-- The unique ambient face fails the root-free boundary-component coherence target: the two
selected-boundary edges on that face lie in different connected components of the shared-endpoint
support graph. -/
theorem not_boundaryComponentReachableOnFace_onlyFace :
    ¬ BoundaryComponentReachableOnFace (emb := badEmbedding) onlyFace := by
  intro hreach
  have h01Face : e01 ∈ badEmbedding.faceBoundary onlyFace.1 := by
    simp [badEmbedding, badFaceBoundary, onlyFace, e01]
  have h23Face : e23 ∈ badEmbedding.faceBoundary onlyFace.1 := by
    simp [badEmbedding, badFaceBoundary, onlyFace, e23]
  exact not_reachable_be01_be23 (hreach h01Face h23Face hs01 hs23)

theorem not_boundarySelectedBoundaryArcOnFace_onlyFace :
    ¬ BoundarySelectedBoundaryArcOnFace (emb := badEmbedding) onlyFace := by
  intro harc
  exact not_boundaryComponentReachableOnFace_onlyFace
    (boundaryComponentReachableOnFace_of_boundarySelectedBoundaryArcOnFace harc)

theorem boundarySelectedBoundaryArcOnFace_of_faceBoundaryEndpointRun_onlyFace
    (faceRun : FaceBoundaryEndpointRun badEmbedding onlyFace) :
    BoundarySelectedBoundaryArcOnFace (emb := badEmbedding) onlyFace := by
  refine ⟨faceRun, faceRun.run, ?_, ?_⟩
  · simp
  · intro e
    constructor
    · intro he
      have hFace : e ∈ badEmbedding.faceBoundary onlyFace.1 := (faceRun.hmem e).1 he
      exact ⟨hFace, (mem_selectedBoundarySupport_iff_mem_onlyFaceBoundary).2 hFace⟩
    · intro he
      exact (faceRun.hmem e).2 he.1

/-- The stronger bundled local face-boundary geometry target genuinely fails on the current API:
the bad embedding admits no per-face ordered run plus selected-boundary arc package. -/
theorem not_nonempty_planarBoundarySelectedBoundaryArcGeometry_badEmbedding :
    ¬ Nonempty (PlanarBoundarySelectedBoundaryArcGeometry badEmbedding) := by
  rintro ⟨geom⟩
  exact not_boundarySelectedBoundaryArcOnFace_onlyFace
    (geom.boundarySelectedBoundaryArcOnFace onlyFace)

theorem not_nonempty_planarBoundaryOrderedFaceArcEmbeddingData_badEmbedding :
    ¬ Nonempty (PlanarBoundaryOrderedFaceArcEmbeddingData badEmbedding) := by
  rintro ⟨data⟩
  exact not_nonempty_planarBoundarySelectedBoundaryArcGeometry_badEmbedding
    ⟨data.toPlanarBoundarySelectedBoundaryArcGeometry⟩

/-- The pure ordered face-boundary run target already fails: if the unique face boundary admitted
any endpoint-sharing run, then because every boundary edge is selected, that run would induce the
forbidden selected-boundary arc geometry above. -/
theorem not_nonempty_planarBoundaryFaceBoundaryRunGeometry_badEmbedding :
    ¬ Nonempty (PlanarBoundaryFaceBoundaryRunGeometry badEmbedding) := by
  exact OrderedPlanarEmbeddingWithBoundaryRegression.not_nonempty_faceBoundaryRunGeometry_badEmbedding

/-- The new generic stronger source object already fails on the bad embedding: there is no way to
equip its unique face boundary with an endpoint-sharing order that lists exactly the two disjoint
edges. -/
theorem not_nonempty_orderedFaceBoundaryData_badEmbedding :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData badEmbedding) := by
  exact OrderedPlanarEmbeddingWithBoundaryRegression.not_nonempty_orderedFaceBoundaryData_badEmbedding

theorem not_nonempty_planarBoundaryOrderedFaceEmbeddingData_badEmbedding :
    ¬ Nonempty (PlanarBoundaryOrderedFaceEmbeddingData badEmbedding) := by
  simpa using not_nonempty_orderedFaceBoundaryData_badEmbedding

theorem not_nonempty_planarBoundaryOrderedFaceVertexEmbeddingData_badEmbedding :
    ¬ Nonempty (PlanarBoundaryOrderedFaceVertexEmbeddingData badEmbedding) := by
  rw [← nonempty_planarBoundaryOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryOrderedFaceVertexEmbeddingData]
  exact not_nonempty_planarBoundaryOrderedFaceEmbeddingData_badEmbedding

theorem not_nonempty_planarBoundaryOrderedFaceVertexSequenceEmbeddingData_badEmbedding :
    ¬ Nonempty (PlanarBoundaryOrderedFaceVertexSequenceEmbeddingData badEmbedding) := by
  rw
    [← nonempty_planarBoundaryOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryOrderedFaceVertexSequenceEmbeddingData]
  exact not_nonempty_planarBoundaryOrderedFaceEmbeddingData_badEmbedding

theorem not_nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_badEmbedding :
    ¬ Nonempty (PlanarBoundaryCyclicOrderedFaceEmbeddingData badEmbedding) := by
  exact OrderedPlanarEmbeddingWithBoundaryRegression.not_nonempty_cyclicOrderedFaceBoundaryData_badEmbedding

theorem not_nonempty_planarBoundaryCyclicFaceBoundaryRunGeometry_badEmbedding :
    ¬ Nonempty (PlanarBoundaryCyclicFaceBoundaryRunGeometry badEmbedding) := by
  exact OrderedPlanarEmbeddingWithBoundaryRegression.not_nonempty_faceBoundaryClosedRunGeometry_badEmbedding

theorem not_nonempty_planarBoundaryCyclicFaceBoundaryVertexWalkGeometry_badEmbedding :
    ¬ Nonempty (PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry badEmbedding) := by
  exact
    OrderedPlanarEmbeddingWithBoundaryRegression.not_nonempty_faceBoundaryClosedVertexWalkGeometry_badEmbedding

theorem not_nonempty_planarBoundaryCyclicOrderedFaceVertexEmbeddingData_badEmbedding :
    ¬ Nonempty (PlanarBoundaryCyclicOrderedFaceVertexEmbeddingData badEmbedding) := by
  rw
    [← nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryCyclicOrderedFaceVertexEmbeddingData]
  exact not_nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_badEmbedding

theorem not_nonempty_planarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData_badEmbedding :
    ¬ Nonempty (PlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData badEmbedding) := by
  rw
    [← nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData]
  exact not_nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_badEmbedding

theorem mem_selectedBoundarySupport_path (e : pathGraph.edgeSet) :
    e ∈ selectedBoundarySupport pathEmbedding.faceBoundary pathEmbedding.faces pathEmbedding.faces := by
  rcases path_edge_eq_p01_or_p12_or_p23 e with rfl | rfl | rfl <;>
    simp [selectedBoundarySupport, totalIncidenceCount, pathEmbedding, pathFaces, pathFaceBoundary]

/-- The path embedding supports the full ordered face-arc interface when the selected arc is the
entire face boundary. This is the linear-but-not-cyclic counterexample for the stronger
source-facing FourColor layer. -/
def pathOrderedFaceArcEmbeddingData : PlanarBoundaryOrderedFaceArcEmbeddingData pathEmbedding where
  faceBoundaryOrder := pathOrderedFaceBoundaryData.faceBoundaryOrder
  hchain := pathOrderedFaceBoundaryData.hchain
  hnodup := pathOrderedFaceBoundaryData.hnodup
  hmem := pathOrderedFaceBoundaryData.hmem
  selectedBoundaryArc := by
    intro f
    refine ⟨pathOrderedFaceBoundaryData.faceBoundaryOrder f, ?_, ?_⟩
    · simp
    · intro e
      constructor
      · intro he
        exact ⟨(pathOrderedFaceBoundaryData.hmem f e).1 he, mem_selectedBoundarySupport_path e⟩
      · intro he
        exact (pathOrderedFaceBoundaryData.hmem f e).2 he.1

noncomputable def pathOrderedFaceVertexEmbeddingData :
    PlanarBoundaryOrderedFaceVertexEmbeddingData pathEmbedding :=
  pathOrderedFaceBoundaryData.toOrderedFaceBoundaryVertexData

noncomputable def pathOrderedFaceVertexSequenceEmbeddingData :
    PlanarBoundaryOrderedFaceVertexSequenceEmbeddingData pathEmbedding :=
  pathOrderedFaceBoundaryData.toOrderedFaceBoundaryVertexSequenceData

theorem nonempty_planarBoundaryOrderedFaceVertexEmbeddingData_pathEmbedding :
    Nonempty (PlanarBoundaryOrderedFaceVertexEmbeddingData pathEmbedding) := by
  exact ⟨pathOrderedFaceVertexEmbeddingData⟩

theorem nonempty_planarBoundaryOrderedFaceVertexSequenceEmbeddingData_pathEmbedding :
    Nonempty (PlanarBoundaryOrderedFaceVertexSequenceEmbeddingData pathEmbedding) := by
  exact ⟨pathOrderedFaceVertexSequenceEmbeddingData⟩

theorem nonempty_planarBoundaryOrderedFaceArcEmbeddingData_pathEmbedding :
    Nonempty (PlanarBoundaryOrderedFaceArcEmbeddingData pathEmbedding) := by
  exact ⟨pathOrderedFaceArcEmbeddingData⟩

theorem nonempty_planarBoundarySelectedBoundaryArcGeometry_pathEmbedding :
    Nonempty (PlanarBoundarySelectedBoundaryArcGeometry pathEmbedding) := by
  exact ⟨pathOrderedFaceArcEmbeddingData.toPlanarBoundarySelectedBoundaryArcGeometry⟩

theorem not_nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_pathEmbedding :
    ¬ Nonempty (PlanarBoundaryCyclicOrderedFaceEmbeddingData pathEmbedding) := by
  exact OrderedPlanarEmbeddingWithBoundaryRegression.not_nonempty_cyclicOrderedFaceBoundaryData_pathEmbedding

theorem not_nonempty_planarBoundaryCyclicOrderedFaceVertexEmbeddingData_pathEmbedding :
    ¬ Nonempty (PlanarBoundaryCyclicOrderedFaceVertexEmbeddingData pathEmbedding) := by
  rw
    [← nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryCyclicOrderedFaceVertexEmbeddingData]
  exact not_nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_pathEmbedding

theorem not_nonempty_planarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData_pathEmbedding :
    ¬ Nonempty (PlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData pathEmbedding) := by
  rw
    [← nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData]
  exact not_nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_pathEmbedding

theorem not_nonempty_planarBoundaryCyclicFaceBoundaryRunGeometry_pathEmbedding :
    ¬ Nonempty (PlanarBoundaryCyclicFaceBoundaryRunGeometry pathEmbedding) := by
  exact OrderedPlanarEmbeddingWithBoundaryRegression.not_nonempty_faceBoundaryClosedRunGeometry_pathEmbedding

theorem not_nonempty_planarBoundaryCyclicFaceBoundaryVertexWalkGeometry_pathEmbedding :
    ¬ Nonempty (PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry pathEmbedding) := by
  exact
    OrderedPlanarEmbeddingWithBoundaryRegression.not_nonempty_faceBoundaryClosedVertexWalkGeometry_pathEmbedding

theorem not_nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_pathEmbedding :
    ¬ Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData pathEmbedding) := by
  rintro ⟨data⟩
  exact not_nonempty_planarBoundaryCyclicOrderedFaceEmbeddingData_pathEmbedding
    ⟨data.toPlanarBoundaryCyclicOrderedFaceEmbeddingData⟩

private theorem path_sym2_edges_length_le_three {l : List (Sym2 (Fin 4))} (hnodup : l.Nodup)
    (hmem : ∀ e ∈ l, e = s(0, 1) ∨ e = s(1, 2) ∨ e = s(2, 3)) :
    l.length ≤ 3 := by
  have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnodup
  rw [← hcard]
  have hsubset : l.toFinset ⊆ ({s(0, 1), s(1, 2), s(2, 3)} : Finset (Sym2 (Fin 4))) := by
    intro e he
    rcases List.mem_toFinset.mp he with he'
    rcases hmem e he' with rfl | rfl | rfl <;> simp
  have hcard_le := Finset.card_le_card hsubset
  simpa using hcard_le

theorem path_no_triangle {a b c : Fin 4} :
    ¬ (pathGraph.Adj a b ∧ pathGraph.Adj b c ∧ pathGraph.Adj c a) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [pathGraph]

theorem path_edges_length_le_three {v w : Fin 4} (p : pathGraph.Walk v w) (htrail : p.IsTrail) :
    p.length ≤ 3 := by
  have hsub : ∀ e ∈ p.edges, e = s(0, 1) ∨ e = s(1, 2) ∨ e = s(2, 3) := by
    intro e he
    have hedge : e ∈ pathGraph.edgeSet := p.edges_subset_edgeSet he
    have h : (e = s(0, 1) ∨ e = s(1, 2) ∨ e = s(2, 3)) ∧ ¬ e.IsDiag := by
      simpa [pathGraph] using hedge
    exact h.1
  have hle_edges : p.edges.length ≤ 3 := path_sym2_edges_length_le_three htrail.edges_nodup hsub
  simpa [SimpleGraph.Walk.length_edges] using hle_edges

/-- The three-edge path graph is acyclic: any cycle would have length exactly `3`, hence would
give a triangle, but the path has no triangle. -/
theorem pathGraph_isAcyclic : pathGraph.IsAcyclic := by
  intro v c hc
  have hle : c.length ≤ 3 := path_edges_length_le_three c hc.isTrail
  have hge : 3 ≤ c.length := hc.three_le_length
  have hlen : c.length = 3 := by omega
  cases c with
  | nil => simp at hlen
  | cons h1 c1 =>
      cases c1 with
      | nil => simp at hlen
      | cons h2 c2 =>
          cases c2 with
          | nil => simp at hlen
          | cons h3 c3 =>
              cases c3 with
              | nil =>
                  exact path_no_triangle ⟨h1, h2, h3⟩
              | cons h4 c4 =>
                  simp at hlen

/-- No embedding of the three-edge path graph can admit the honest facial closed-walk source
interface: any such witness would give a nonempty closed trail in an acyclic graph. -/
theorem not_nonempty_planarBoundaryClosedWalkEmbeddingData_pathGraph
    {emb : PlaneEmbeddingWithBoundary pathGraph} :
    ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) := by
  exact
    not_nonempty_planarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      pathGraph_isAcyclic ⟨p01⟩

theorem not_nonempty_planarBoundaryClosedWalkEmbeddingData_pathEmbedding :
    ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData pathEmbedding) := by
  exact not_nonempty_planarBoundaryClosedWalkEmbeddingData_pathGraph

theorem exists_embedding_withPlanarBoundaryOrderedFaceArcEmbeddingData_withoutCyclicOrderedFaceArcEmbeddingData :
    ∃ emb : PlaneEmbeddingWithBoundary pathGraph,
      Nonempty (PlanarBoundaryOrderedFaceArcEmbeddingData emb) ∧
        ¬ Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) := by
  exact ⟨pathEmbedding, nonempty_planarBoundaryOrderedFaceArcEmbeddingData_pathEmbedding,
    not_nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_pathEmbedding⟩

theorem exists_embedding_withPlanarBoundaryOrderedFaceArcEmbeddingData_withoutClosedWalkEmbeddingData :
    ∃ emb : PlaneEmbeddingWithBoundary pathGraph,
      Nonempty (PlanarBoundaryOrderedFaceArcEmbeddingData emb) ∧
        ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) := by
  exact ⟨pathEmbedding, nonempty_planarBoundaryOrderedFaceArcEmbeddingData_pathEmbedding,
    not_nonempty_planarBoundaryClosedWalkEmbeddingData_pathEmbedding⟩

theorem exists_embedding_withPlanarBoundaryOrderedFaceVertexEmbeddingData_withoutCyclicOrderedFaceVertexEmbeddingData :
    ∃ emb : PlaneEmbeddingWithBoundary pathGraph,
      Nonempty (PlanarBoundaryOrderedFaceVertexEmbeddingData emb) ∧
        ¬ Nonempty (PlanarBoundaryCyclicOrderedFaceVertexEmbeddingData emb) := by
  exact ⟨pathEmbedding, nonempty_planarBoundaryOrderedFaceVertexEmbeddingData_pathEmbedding,
    not_nonempty_planarBoundaryCyclicOrderedFaceVertexEmbeddingData_pathEmbedding⟩

theorem
    exists_embedding_withPlanarBoundaryOrderedFaceVertexSequenceEmbeddingData_withoutCyclicOrderedFaceVertexSequenceEmbeddingData :
    ∃ emb : PlaneEmbeddingWithBoundary pathGraph,
      Nonempty (PlanarBoundaryOrderedFaceVertexSequenceEmbeddingData emb) ∧
        ¬ Nonempty (PlanarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData emb) := by
  exact ⟨pathEmbedding, nonempty_planarBoundaryOrderedFaceVertexSequenceEmbeddingData_pathEmbedding,
    not_nonempty_planarBoundaryCyclicOrderedFaceVertexSequenceEmbeddingData_pathEmbedding⟩

theorem
    exists_embedding_withPlanarBoundaryOrderedFaceVertexSequenceEmbeddingData_withoutCyclicFaceBoundaryVertexWalkGeometry :
    ∃ emb : PlaneEmbeddingWithBoundary pathGraph,
      Nonempty (PlanarBoundaryOrderedFaceVertexSequenceEmbeddingData emb) ∧
        ¬ Nonempty (PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb) := by
  exact ⟨pathEmbedding, nonempty_planarBoundaryOrderedFaceVertexSequenceEmbeddingData_pathEmbedding,
    not_nonempty_planarBoundaryCyclicFaceBoundaryVertexWalkGeometry_pathEmbedding⟩

theorem exists_embedding_withPlanarBoundarySelectedBoundaryArcGeometry_withoutCyclicOrderedFaceArcEmbeddingData :
    ∃ emb : PlaneEmbeddingWithBoundary pathGraph,
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
        ¬ Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) := by
  exact ⟨pathEmbedding, nonempty_planarBoundarySelectedBoundaryArcGeometry_pathEmbedding,
    not_nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_pathEmbedding⟩

theorem admitsPlanarBoundarySelectedBoundaryArcGeometry_pathGraph :
    AdmitsPlanarBoundarySelectedBoundaryArcGeometry pathGraph := by
  exact ⟨pathEmbedding, nonempty_planarBoundarySelectedBoundaryArcGeometry_pathEmbedding⟩

theorem admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace_pathGraph :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace pathGraph := by
  exact
    (admitsPlanarBoundarySelectedBoundaryArcGeometry_iff_admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace).1
      admitsPlanarBoundarySelectedBoundaryArcGeometry_pathGraph

theorem exists_embedding_withPlanarBoundaryFaceBoundaryRunGeometry_withoutCyclicFaceBoundaryRunGeometry :
    ∃ emb : PlaneEmbeddingWithBoundary pathGraph,
      Nonempty (PlanarBoundaryFaceBoundaryRunGeometry emb) ∧
        ¬ Nonempty (PlanarBoundaryCyclicFaceBoundaryRunGeometry emb) := by
  exact
    ⟨pathEmbedding,
      (nonempty_planarBoundaryOrderedFaceEmbeddingData_iff_nonempty_planarBoundaryFaceBoundaryRunGeometry).1
        OrderedPlanarEmbeddingWithBoundaryRegression.nonempty_orderedFaceBoundaryData_pathEmbedding,
      not_nonempty_planarBoundaryCyclicFaceBoundaryRunGeometry_pathEmbedding⟩

theorem admitsPlanarBoundaryOrderedFaceArcEmbeddingData_pathGraph :
    AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData pathGraph := by
  exact ⟨pathEmbedding, nonempty_planarBoundaryOrderedFaceArcEmbeddingData_pathEmbedding⟩

theorem not_admitsPlanarBoundaryClosedWalkEmbeddingData_pathGraph :
    ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData pathGraph := by
  exact
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      pathGraph_isAcyclic ⟨p01⟩

/-- The closed-walk annulus-boundary source is impossible on the path graph for the same reason:
its `closedWalks` field would already give an honest facial closed-walk interface. -/
theorem not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_pathGraph :
    ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource pathGraph := by
  exact
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      pathGraph_isAcyclic ⟨p01⟩

theorem admitsPlanarBoundaryOrderedFaceArcEmbeddingData_withoutClosedWalk_pathGraph :
    AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData pathGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData pathGraph := by
  exact ⟨admitsPlanarBoundaryOrderedFaceArcEmbeddingData_pathGraph,
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_pathGraph⟩

theorem
    admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace_withoutClosedWalk_pathGraph :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace pathGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData pathGraph := by
  exact ⟨admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace_pathGraph,
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_pathGraph⟩

theorem
    admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace_withoutClosedWalkAnnulusBoundarySource_pathGraph :
    AdmitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace pathGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource pathGraph := by
  exact ⟨admitsPlanarBoundaryFaceBoundaryRunGeometryAndSelectedBoundaryArcOnFace_pathGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_pathGraph⟩

theorem admitsPlanarBoundaryOrderedFaceArcEmbeddingData_withoutClosedWalkAnnulusBoundarySource_pathGraph :
    AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData pathGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource pathGraph := by
  exact ⟨admitsPlanarBoundaryOrderedFaceArcEmbeddingData_pathGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_pathGraph⟩

theorem mem_selectedBoundarySupport_star (e : starGraph.edgeSet) :
    e ∈ selectedBoundarySupport starEmbedding.faceBoundary starEmbedding.faces starEmbedding.faces := by
  rcases star_edge_eq_s01_or_s02_or_s03 e with rfl | rfl | rfl <;>
    simp [selectedBoundarySupport, totalIncidenceCount, starEmbedding, starFaces, starFaceBoundary]

/-- The star embedding also satisfies the full cyclic face-arc shell on the FourColor side,
because with a single face every boundary edge is selected. This shows the current route-facing
cyclic selected-boundary interface can still exist without any honest facial closed walk. -/
def starCyclicOrderedFaceArcEmbeddingData :
    PlanarBoundaryCyclicOrderedFaceArcEmbeddingData starEmbedding where
  faceBoundaryOrder := starCyclicOrderedFaceBoundaryData.faceBoundaryOrder
  hchain := starCyclicOrderedFaceBoundaryData.hchain
  hnodup := starCyclicOrderedFaceBoundaryData.hnodup
  hmem := starCyclicOrderedFaceBoundaryData.hmem
  selectedBoundaryArc := by
    intro f
    refine ⟨starCyclicOrderedFaceBoundaryData.faceBoundaryOrder f, ?_, ?_⟩
    · simp
    · intro e
      constructor
      · intro he
        exact ⟨(starCyclicOrderedFaceBoundaryData.hmem f e).1 he, mem_selectedBoundarySupport_star e⟩
      · intro he
        exact (starCyclicOrderedFaceBoundaryData.hmem f e).2 he.1
  hwrap := starCyclicOrderedFaceBoundaryData.hwrap

theorem nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_starEmbedding :
    Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData starEmbedding) := by
  exact ⟨starCyclicOrderedFaceArcEmbeddingData⟩

theorem nonempty_planarBoundarySelectedBoundaryArcGeometry_starEmbedding :
    Nonempty (PlanarBoundarySelectedBoundaryArcGeometry starEmbedding) := by
  exact ⟨starCyclicOrderedFaceArcEmbeddingData.toPlanarBoundarySelectedBoundaryArcGeometry⟩

theorem
    nonempty_planarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace_starEmbedding :
    ∃ geom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry starEmbedding,
      ∀ f : AmbientFace starEmbedding.faces,
        (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f := by
  exact
    (nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_iff_exists_planarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace).1
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_starEmbedding

/-- The star graph cannot admit the honest facial closed-walk source interface on any embedding:
any such witness would give a nonempty closed trail in an acyclic graph. -/
theorem not_nonempty_planarBoundaryClosedWalkEmbeddingData_starGraph
    {emb : PlaneEmbeddingWithBoundary starGraph} :
    ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) := by
  exact
    not_nonempty_planarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      starGraph_isAcyclic ⟨s01⟩

theorem not_nonempty_planarBoundaryClosedWalkEmbeddingData_starEmbedding :
    ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData starEmbedding) := by
  exact not_nonempty_planarBoundaryClosedWalkEmbeddingData_starGraph

theorem exists_embedding_withPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_withoutClosedWalkEmbeddingData :
    ∃ emb : PlaneEmbeddingWithBoundary starGraph,
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
        ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) := by
  exact ⟨starEmbedding, nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_starEmbedding,
    not_nonempty_planarBoundaryClosedWalkEmbeddingData_starEmbedding⟩

theorem exists_embedding_withPlanarBoundarySelectedBoundaryArcGeometry_withoutClosedWalkEmbeddingData :
    ∃ emb : PlaneEmbeddingWithBoundary starGraph,
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
        ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) := by
  exact ⟨starEmbedding, nonempty_planarBoundarySelectedBoundaryArcGeometry_starEmbedding,
    not_nonempty_planarBoundaryClosedWalkEmbeddingData_starEmbedding⟩

theorem admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph :
    AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData starGraph := by
  exact ⟨starEmbedding, nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_starEmbedding⟩

theorem admitsPlanarBoundarySelectedBoundaryArcGeometry_starGraph :
    AdmitsPlanarBoundarySelectedBoundaryArcGeometry starGraph := by
  exact ⟨starEmbedding, nonempty_planarBoundarySelectedBoundaryArcGeometry_starEmbedding⟩

theorem
    admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace_starGraph :
    AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace
      starGraph := by
  exact
    (admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_iff_admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace).1
      admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph

theorem not_admitsPlanarBoundaryClosedWalkEmbeddingData_starGraph :
    ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData starGraph := by
  exact
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      starGraph_isAcyclic ⟨s01⟩

/-- No realized facial dart-cycle source exists on the star graph: it would lower to honest
closed facial walks. -/
theorem not_nonempty_planarBoundaryDartCycleEmbeddingData_starGraph
    {emb : PlaneEmbeddingWithBoundary starGraph} :
    ¬ Nonempty (PlanarBoundaryDartCycleEmbeddingData emb) := by
  exact
    not_nonempty_planarBoundaryDartCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      starGraph_isAcyclic ⟨s01⟩

/-- No pure facial dart-cycle source exists on the star graph: the mechanical walk construction
would still lower it to honest closed facial walks. -/
theorem not_nonempty_planarBoundaryPureDartCycleEmbeddingData_starGraph
    {emb : PlaneEmbeddingWithBoundary starGraph} :
    ¬ Nonempty (PlanarBoundaryPureDartCycleEmbeddingData emb) := by
  exact
    not_nonempty_planarBoundaryPureDartCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      starGraph_isAcyclic ⟨s01⟩

/-- No successor-based facial dart-cycle source exists on the star graph: the successor source
lowers to the pure dart-cycle source and then to honest closed facial walks. -/
theorem not_nonempty_planarBoundaryDartSuccessorCycleEmbeddingData_starGraph
    {emb : PlaneEmbeddingWithBoundary starGraph} :
    ¬ Nonempty (PlanarBoundaryDartSuccessorCycleEmbeddingData emb) := by
  exact
    not_nonempty_planarBoundaryDartSuccessorCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      starGraph_isAcyclic ⟨s01⟩

/-- Graph-level realized facial dart cycles are impossible on the star graph. -/
theorem not_admitsPlanarBoundaryDartCycleEmbeddingData_starGraph :
    ¬ AdmitsPlanarBoundaryDartCycleEmbeddingData starGraph := by
  exact
    not_admitsPlanarBoundaryDartCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      starGraph_isAcyclic ⟨s01⟩

/-- Graph-level pure facial dart cycles are impossible on the star graph. -/
theorem not_admitsPlanarBoundaryPureDartCycleEmbeddingData_starGraph :
    ¬ AdmitsPlanarBoundaryPureDartCycleEmbeddingData starGraph := by
  exact
    not_admitsPlanarBoundaryPureDartCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      starGraph_isAcyclic ⟨s01⟩

/-- Graph-level successor-based facial dart cycles are impossible on the star graph. -/
theorem not_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_starGraph :
    ¬ AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData starGraph := by
  exact
    not_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      starGraph_isAcyclic ⟨s01⟩

/-- The closed-walk annulus-boundary source is also impossible on the star graph: its
`closedWalks` field would already give the honest facial closed-walk interface ruled out above.
-/
theorem not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_starGraph :
    ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource starGraph := by
  exact
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      starGraph_isAcyclic ⟨s01⟩

theorem admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_withoutClosedWalk_starGraph :
    AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData starGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData starGraph := by
  exact ⟨admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph,
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_starGraph⟩

/-- The star witness separates the old cyclic selected-boundary shell from the realized dart-cycle
source. -/
theorem admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_withoutDartCycle_starGraph :
    AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData starGraph ∧
      ¬ AdmitsPlanarBoundaryDartCycleEmbeddingData starGraph := by
  exact ⟨admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph,
    not_admitsPlanarBoundaryDartCycleEmbeddingData_starGraph⟩

/-- The star witness separates the old cyclic selected-boundary shell from the pure dart-cycle
source. -/
theorem admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_withoutPureDartCycle_starGraph :
    AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData starGraph ∧
      ¬ AdmitsPlanarBoundaryPureDartCycleEmbeddingData starGraph := by
  exact ⟨admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph,
    not_admitsPlanarBoundaryPureDartCycleEmbeddingData_starGraph⟩

/-- The star witness separates the old cyclic selected-boundary shell from the successor-based
dart-cycle source. -/
theorem admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_withoutDartSuccessorCycle_starGraph :
    AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData starGraph ∧
      ¬ AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData starGraph := by
  exact ⟨admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph,
    not_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_starGraph⟩

theorem admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_withoutClosedWalkAnnulusBoundarySource_starGraph :
    AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData starGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource starGraph := by
  exact ⟨admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_starGraph⟩

theorem admitsPlanarBoundarySelectedBoundaryArcGeometry_withoutClosedWalk_starGraph :
    AdmitsPlanarBoundarySelectedBoundaryArcGeometry starGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData starGraph := by
  exact ⟨admitsPlanarBoundarySelectedBoundaryArcGeometry_starGraph,
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_starGraph⟩

theorem
    admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace_withoutClosedWalk_starGraph :
    AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace
        starGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData starGraph := by
  exact ⟨admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace_starGraph,
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_starGraph⟩

theorem
    admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace_withoutClosedWalkAnnulusBoundarySource_starGraph :
    AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace
        starGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource starGraph := by
  exact ⟨admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace_starGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_starGraph⟩

/-- Two disjoint three-stars. This is the smallest current same-embedding witness that carries a
two-component annulus boundary partition together with cyclic selected-boundary face arcs, while
still being too weak to force honest facial closed walks. -/
def doubleStarGraph : SimpleGraph (Fin 8) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(0, 2), s(0, 3), s(4, 5), s(4, 6), s(4, 7)} : Set (Sym2 (Fin 8)))

def ds01 : doubleStarGraph.edgeSet := ⟨s(0, 1), by simp [doubleStarGraph]⟩
def ds02 : doubleStarGraph.edgeSet := ⟨s(0, 2), by simp [doubleStarGraph]⟩
def ds03 : doubleStarGraph.edgeSet := ⟨s(0, 3), by simp [doubleStarGraph]⟩
def ds45 : doubleStarGraph.edgeSet := ⟨s(4, 5), by simp [doubleStarGraph]⟩
def ds46 : doubleStarGraph.edgeSet := ⟨s(4, 6), by simp [doubleStarGraph]⟩
def ds47 : doubleStarGraph.edgeSet := ⟨s(4, 7), by simp [doubleStarGraph]⟩

theorem ds01_ne_ds02 : ds01 ≠ ds02 := by
  intro h
  have := congrArg Subtype.val h
  simp [ds01, ds02] at this

theorem ds01_ne_ds03 : ds01 ≠ ds03 := by
  intro h
  have := congrArg Subtype.val h
  simp [ds01, ds03] at this

theorem ds02_ne_ds03 : ds02 ≠ ds03 := by
  intro h
  have := congrArg Subtype.val h
  simp [ds02, ds03] at this

theorem ds45_ne_ds46 : ds45 ≠ ds46 := by
  intro h
  have := congrArg Subtype.val h
  simp [ds45, ds46] at this

theorem ds45_ne_ds47 : ds45 ≠ ds47 := by
  intro h
  have := congrArg Subtype.val h
  simp [ds45, ds47] at this

theorem ds46_ne_ds47 : ds46 ≠ ds47 := by
  intro h
  have := congrArg Subtype.val h
  simp [ds46, ds47] at this

theorem doubleStar_edge_eq_cases (e : doubleStarGraph.edgeSet) :
    e = ds01 ∨ e = ds02 ∨ e = ds03 ∨ e = ds45 ∨ e = ds46 ∨ e = ds47 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(0, 2) ∨ e.1 = s(0, 3) ∨
        e.1 = s(4, 5) ∨ e.1 = s(4, 6) ∨ e.1 = s(4, 7)) ∧
        ¬ e.1.IsDiag := by
    simpa [doubleStarGraph] using e.2
  rcases h.1 with h01 | h02 | h03 | h45 | h46 | h47
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr <| Or.inl (Subtype.ext h02)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h03)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h46)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext h47)

abbrev DoubleStarFace := Fin 2

def doubleStarFaces : Finset DoubleStarFace := Finset.univ

def doubleStarFaceBoundary : DoubleStarFace → Finset doubleStarGraph.edgeSet
  | ⟨0, _⟩ => {ds01, ds02, ds03}
  | ⟨1, _⟩ => {ds45, ds46, ds47}

def doubleStarEmbedding : PlaneEmbeddingWithBoundary doubleStarGraph where
  Face := DoubleStarFace
  faceDecidableEq := inferInstance
  faces := doubleStarFaces
  faceBoundary := doubleStarFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases doubleStar_edge_eq_cases e with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  edge_one_or_two_faces := by
    intro e _he
    rcases doubleStar_edge_eq_cases e with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def doubleLeftFaceIdx : DoubleStarFace := ⟨0, by decide⟩
def doubleRightFaceIdx : DoubleStarFace := ⟨1, by decide⟩

def doubleLeftFace : AmbientFace doubleStarEmbedding.faces :=
  ⟨doubleLeftFaceIdx, by simp [doubleStarEmbedding, doubleStarFaces, doubleLeftFaceIdx]⟩

def doubleRightFace : AmbientFace doubleStarEmbedding.faces :=
  ⟨doubleRightFaceIdx, by simp [doubleStarEmbedding, doubleStarFaces, doubleRightFaceIdx]⟩

theorem doubleStarFace_eq_cases (f : AmbientFace doubleStarEmbedding.faces) :
    f = doubleLeftFace ∨ f = doubleRightFace := by
  rcases f with ⟨f, hf⟩
  change DoubleStarFace at f
  fin_cases f <;>
    simp [doubleLeftFace, doubleRightFace, doubleLeftFaceIdx, doubleRightFaceIdx,
      doubleStarEmbedding, doubleStarFaces] at *

theorem planarEmbeddingBoundaryEdgeEndpointAdj_ds01_ds02 :
    planarEmbeddingBoundaryEdgeEndpointAdj ds01 ds02 := by
  refine ⟨ds01_ne_ds02, 0, ?_, ?_⟩ <;> simp [ds01, ds02]

theorem planarEmbeddingBoundaryEdgeEndpointAdj_ds02_ds03 :
    planarEmbeddingBoundaryEdgeEndpointAdj ds02 ds03 := by
  refine ⟨ds02_ne_ds03, 0, ?_, ?_⟩ <;> simp [ds02, ds03]

theorem planarEmbeddingBoundaryEdgeEndpointAdj_ds03_ds01 :
    planarEmbeddingBoundaryEdgeEndpointAdj ds03 ds01 := by
  refine ⟨ds01_ne_ds03.symm, 0, ?_, ?_⟩ <;> simp [ds03, ds01]

theorem planarEmbeddingBoundaryEdgeEndpointAdj_ds45_ds46 :
    planarEmbeddingBoundaryEdgeEndpointAdj ds45 ds46 := by
  refine ⟨ds45_ne_ds46, 4, ?_, ?_⟩ <;> simp [ds45, ds46]

theorem planarEmbeddingBoundaryEdgeEndpointAdj_ds46_ds47 :
    planarEmbeddingBoundaryEdgeEndpointAdj ds46 ds47 := by
  refine ⟨ds46_ne_ds47, 4, ?_, ?_⟩ <;> simp [ds46, ds47]

theorem planarEmbeddingBoundaryEdgeEndpointAdj_ds47_ds45 :
    planarEmbeddingBoundaryEdgeEndpointAdj ds47 ds45 := by
  refine ⟨ds45_ne_ds47.symm, 4, ?_, ?_⟩ <;> simp [ds47, ds45]

def doubleStarCyclicOrderedFaceBoundaryData :
    PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData doubleStarEmbedding where
  faceBoundaryOrder
    | ⟨⟨0, _⟩, _⟩ => [ds01, ds02, ds03]
    | ⟨⟨1, _⟩, _⟩ => [ds45, ds46, ds47]
  hchain := by
    intro f
    rcases doubleStarFace_eq_cases f with rfl | rfl
    · exact (List.isChain_cons_cons).2
        ⟨planarEmbeddingBoundaryEdgeEndpointAdj_ds01_ds02,
          (List.isChain_pair).2 planarEmbeddingBoundaryEdgeEndpointAdj_ds02_ds03⟩
    · exact (List.isChain_cons_cons).2
        ⟨planarEmbeddingBoundaryEdgeEndpointAdj_ds45_ds46,
          (List.isChain_pair).2 planarEmbeddingBoundaryEdgeEndpointAdj_ds46_ds47⟩
  hnodup := by
    intro f
    rcases doubleStarFace_eq_cases f with rfl | rfl <;> decide
  hmem := by
    intro f e
    rcases doubleStarFace_eq_cases f with rfl | rfl
    · rcases doubleStar_edge_eq_cases e with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [doubleStarEmbedding, doubleStarFaceBoundary, doubleLeftFace, doubleLeftFaceIdx]
    · rcases doubleStar_edge_eq_cases e with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [doubleStarEmbedding, doubleStarFaceBoundary, doubleRightFace, doubleRightFaceIdx]
  hwrap := by
    intro f first last hfirst hlast
    rcases doubleStarFace_eq_cases f with rfl | rfl
    · have hfirst' : some ds01 = some first := by
        simpa [doubleLeftFace, doubleLeftFaceIdx] using hfirst
      have hlast' : some ds03 = some last := by
        simpa [doubleLeftFace, doubleLeftFaceIdx] using hlast
      have hfirst'' : first = ds01 := by simpa using hfirst'.symm
      have hlast'' : last = ds03 := by simpa using hlast'.symm
      subst first
      subst last
      exact planarEmbeddingBoundaryEdgeEndpointAdj_ds03_ds01
    · have hfirst' : some ds45 = some first := by
        simpa [doubleRightFace, doubleRightFaceIdx] using hfirst
      have hlast' : some ds47 = some last := by
        simpa [doubleRightFace, doubleRightFaceIdx] using hlast
      have hfirst'' : first = ds45 := by simpa using hfirst'.symm
      have hlast'' : last = ds47 := by simpa using hlast'.symm
      subst first
      subst last
      exact planarEmbeddingBoundaryEdgeEndpointAdj_ds47_ds45

theorem mem_selectedBoundarySupport_doubleStar (e : doubleStarGraph.edgeSet) :
    e ∈ selectedBoundarySupport
      doubleStarEmbedding.faceBoundary doubleStarEmbedding.faces doubleStarEmbedding.faces := by
  rcases doubleStar_edge_eq_cases e with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

def doubleStarCyclicOrderedFaceArcEmbeddingData :
    PlanarBoundaryCyclicOrderedFaceArcEmbeddingData doubleStarEmbedding where
  faceBoundaryOrder := doubleStarCyclicOrderedFaceBoundaryData.faceBoundaryOrder
  hchain := doubleStarCyclicOrderedFaceBoundaryData.hchain
  hnodup := doubleStarCyclicOrderedFaceBoundaryData.hnodup
  hmem := doubleStarCyclicOrderedFaceBoundaryData.hmem
  selectedBoundaryArc := by
    intro f
    refine ⟨doubleStarCyclicOrderedFaceBoundaryData.faceBoundaryOrder f, ?_, ?_⟩
    · simp
    · intro e
      constructor
      · intro he
        exact ⟨(doubleStarCyclicOrderedFaceBoundaryData.hmem f e).1 he,
          mem_selectedBoundarySupport_doubleStar e⟩
      · intro he
        exact (doubleStarCyclicOrderedFaceBoundaryData.hmem f e).2 he.1
  hwrap := doubleStarCyclicOrderedFaceBoundaryData.hwrap

theorem nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_doubleStarEmbedding :
    Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData doubleStarEmbedding) := by
  exact ⟨doubleStarCyclicOrderedFaceArcEmbeddingData⟩

theorem nonempty_planarBoundarySelectedBoundaryArcGeometry_doubleStarEmbedding :
    Nonempty (PlanarBoundarySelectedBoundaryArcGeometry doubleStarEmbedding) := by
  exact ⟨doubleStarCyclicOrderedFaceArcEmbeddingData.toPlanarBoundarySelectedBoundaryArcGeometry⟩

def doubleStarOuterRoot : PlanarBoundaryEdgeVertex doubleStarEmbedding :=
  ⟨ds01, mem_selectedBoundarySupport_doubleStar ds01⟩

def doubleStarInnerRoot : PlanarBoundaryEdgeVertex doubleStarEmbedding :=
  ⟨ds45, mem_selectedBoundarySupport_doubleStar ds45⟩

def doubleStarBoundaryLabel (e : PlanarBoundaryEdgeVertex doubleStarEmbedding) : Bool :=
  if e.1 = ds45 ∨ e.1 = ds46 ∨ e.1 = ds47 then true else false

theorem doubleStar_boundaryEdge_eq (e : PlanarBoundaryEdgeVertex doubleStarEmbedding) :
    e = ⟨ds01, mem_selectedBoundarySupport_doubleStar ds01⟩ ∨
      e = ⟨ds02, mem_selectedBoundarySupport_doubleStar ds02⟩ ∨
      e = ⟨ds03, mem_selectedBoundarySupport_doubleStar ds03⟩ ∨
      e = ⟨ds45, mem_selectedBoundarySupport_doubleStar ds45⟩ ∨
      e = ⟨ds46, mem_selectedBoundarySupport_doubleStar ds46⟩ ∨
      e = ⟨ds47, mem_selectedBoundarySupport_doubleStar ds47⟩ := by
  rcases doubleStar_edge_eq_cases e.1 with h01 | h02 | h03 | h45 | h46 | h47
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr <| Or.inl (Subtype.ext h02)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h03)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h46)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext h47)

theorem doubleStarBoundaryAdj_preserves_label :
    ∀ ⦃e f : PlanarBoundaryEdgeVertex doubleStarEmbedding⦄,
      (planarBoundarySupportEndpointAdjGraph doubleStarEmbedding).Adj e f →
        doubleStarBoundaryLabel e = doubleStarBoundaryLabel f := by
  intro e f hadj
  rcases doubleStar_boundaryEdge_eq e with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases doubleStar_boundaryEdge_eq f with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact False.elim
          (by
            rcases hadj with ⟨_, v, hvE, hvF⟩
            fin_cases v <;>
              simp [ds01, ds02, ds03, ds45, ds46, ds47] at hvE hvF)

theorem doubleStarOuterRoot_ne_innerRoot :
    doubleStarOuterRoot ≠ doubleStarInnerRoot := by
  intro h
  have := congrArg Subtype.val h
  simp [doubleStarOuterRoot, doubleStarInnerRoot, ds01, ds45] at this

def doubleStarAnnulusBoundaryReachabilityData :
    PlanarBoundaryAnnulusBoundaryReachabilityData doubleStarEmbedding where
  outerRoot := doubleStarOuterRoot
  innerRoot := doubleStarInnerRoot
  hroots_ne := doubleStarOuterRoot_ne_innerRoot
  hcoverRoots := by
    intro e
    rcases doubleStar_boundaryEdge_eq e with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨doubleStarOuterRoot, by simp [doubleStarOuterRoot_ne_innerRoot],
        SimpleGraph.Reachable.refl _⟩
    · refine ⟨doubleStarOuterRoot, by simp [doubleStarOuterRoot_ne_innerRoot], ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph doubleStarEmbedding).Adj
            ⟨ds02, mem_selectedBoundarySupport_doubleStar ds02⟩
            doubleStarOuterRoot := by
        refine ⟨?_, 0, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [doubleStarOuterRoot, ds02, ds01] at this
        · simp [ds02]
        · simp [doubleStarOuterRoot, ds01]
      exact hadj.reachable
    · refine ⟨doubleStarOuterRoot, by simp [doubleStarOuterRoot_ne_innerRoot], ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph doubleStarEmbedding).Adj
            ⟨ds03, mem_selectedBoundarySupport_doubleStar ds03⟩
            doubleStarOuterRoot := by
        refine ⟨?_, 0, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [doubleStarOuterRoot, ds03, ds01] at this
        · simp [ds03]
        · simp [doubleStarOuterRoot, ds01]
      exact hadj.reachable
    · refine ⟨doubleStarInnerRoot, by simp, SimpleGraph.Reachable.refl _⟩
    · refine ⟨doubleStarInnerRoot, by simp, ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph doubleStarEmbedding).Adj
            ⟨ds46, mem_selectedBoundarySupport_doubleStar ds46⟩
            doubleStarInnerRoot := by
        refine ⟨?_, 4, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [doubleStarInnerRoot, ds46, ds45] at this
        · simp [ds46]
        · simp [doubleStarInnerRoot, ds45]
      exact hadj.reachable
    · refine ⟨doubleStarInnerRoot, by simp, ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph doubleStarEmbedding).Adj
            ⟨ds47, mem_selectedBoundarySupport_doubleStar ds47⟩
            doubleStarInnerRoot := by
        refine ⟨?_, 4, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [doubleStarInnerRoot, ds47, ds45] at this
        · simp [ds47]
        · simp [doubleStarInnerRoot, ds45]
      exact hadj.reachable
  hsepRoots := by
    intro r s hr hs hreach
    have hlabelEq :
        doubleStarBoundaryLabel r = doubleStarBoundaryLabel s :=
      eq_of_reachable_of_eq_on_adj
        (planarBoundarySupportEndpointAdjGraph doubleStarEmbedding)
        doubleStarBoundaryLabel
        (by
          intro u v huv
          exact doubleStarBoundaryAdj_preserves_label huv)
        hreach
    have hOuterLabel : doubleStarBoundaryLabel doubleStarOuterRoot = false := by
      decide
    have hInnerLabel : doubleStarBoundaryLabel doubleStarInnerRoot = true := by
      decide
    have hr_cases : r = doubleStarOuterRoot ∨ r = doubleStarInnerRoot := by
      simpa [doubleStarOuterRoot_ne_innerRoot] using hr
    have hs_cases : s = doubleStarOuterRoot ∨ s = doubleStarInnerRoot := by
      simpa [doubleStarOuterRoot_ne_innerRoot] using hs
    rcases hr_cases with rfl | rfl <;> rcases hs_cases with rfl | rfl
    · rfl
    · rw [hOuterLabel, hInnerLabel] at hlabelEq
      cases hlabelEq
    · rw [hInnerLabel, hOuterLabel] at hlabelEq
      cases hlabelEq
    · rfl

theorem nonempty_planarBoundaryAnnulusBoundaryReachabilityData_doubleStarEmbedding :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData doubleStarEmbedding) := by
  exact ⟨doubleStarAnnulusBoundaryReachabilityData⟩

private theorem doubleStarLeft_sym2_edges_length_le_three {l : List (Sym2 (Fin 8))}
    (hnodup : l.Nodup)
    (hmem : ∀ e ∈ l, e = s(0, 1) ∨ e = s(0, 2) ∨ e = s(0, 3)) :
    l.length ≤ 3 := by
  have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnodup
  rw [← hcard]
  have hsubset : l.toFinset ⊆ ({s(0, 1), s(0, 2), s(0, 3)} : Finset (Sym2 (Fin 8))) := by
    intro e he
    rcases List.mem_toFinset.mp he with he'
    rcases hmem e he' with rfl | rfl | rfl <;> simp
  have hcard_le := Finset.card_le_card hsubset
  simpa using hcard_le

def doubleStarLeftGraph : SimpleGraph (Fin 8) :=
  SimpleGraph.fromEdgeSet ({s(0, 1), s(0, 2), s(0, 3)} : Set (Sym2 (Fin 8)))

theorem doubleStarLeft_adj_iff (u v : Fin 8) :
    doubleStarLeftGraph.Adj u v ↔
      (u = 0 ∧ (v = 1 ∨ v = 2 ∨ v = 3)) ∨
        (v = 0 ∧ (u = 1 ∨ u = 2 ∨ u = 3)) := by
  fin_cases u <;> fin_cases v <;> simp [doubleStarLeftGraph]

theorem doubleStarLeft_adj_left_eq_zero_or_right_eq_zero {u v : Fin 8}
    (h : doubleStarLeftGraph.Adj u v) :
    u = 0 ∨ v = 0 := by
  rcases (doubleStarLeft_adj_iff u v).1 h with h' | h'
  · exact Or.inl h'.1
  · exact Or.inr h'.1

theorem doubleStarLeft_adj_right_eq_zero_of_left_ne_zero {u v : Fin 8}
    (hu : u ≠ 0) (h : doubleStarLeftGraph.Adj u v) :
    v = 0 := by
  rcases doubleStarLeft_adj_left_eq_zero_or_right_eq_zero h with h0 | h0
  · exact False.elim (hu h0)
  · exact h0

theorem doubleStarLeft_adj_left_eq_zero_of_right_ne_zero {u v : Fin 8}
    (hv : v ≠ 0) (h : doubleStarLeftGraph.Adj u v) :
    u = 0 := by
  rcases (doubleStarLeft_adj_iff u v).1 h with h' | h'
  · exact h'.1
  · exact False.elim (hv h'.1)

theorem doubleStarLeft_no_triangle {a b c : Fin 8} :
    ¬ (doubleStarLeftGraph.Adj a b ∧ doubleStarLeftGraph.Adj b c ∧ doubleStarLeftGraph.Adj c a) := by
  rintro ⟨hab, hbc, hca⟩
  by_cases ha : a = 0
  · subst a
    have hc_ne : c ≠ 0 := by
      intro hc
      subst hc
      exact hca.ne rfl
    have hb0 : b = 0 := doubleStarLeft_adj_left_eq_zero_of_right_ne_zero hc_ne hbc
    subst b
    exact hab.ne rfl
  · have hb0 : b = 0 := doubleStarLeft_adj_right_eq_zero_of_left_ne_zero ha hab
    have hc0 : c = 0 := doubleStarLeft_adj_left_eq_zero_of_right_ne_zero ha hca
    subst b
    subst c
    exact hbc.ne rfl

theorem doubleStarLeft_edges_length_le_three {v w : Fin 8}
    (p : doubleStarLeftGraph.Walk v w) (htrail : p.IsTrail) :
    p.length ≤ 3 := by
  have hsub : ∀ e ∈ p.edges, e = s(0, 1) ∨ e = s(0, 2) ∨ e = s(0, 3) := by
    intro e he
    have hedge : e ∈ doubleStarLeftGraph.edgeSet := p.edges_subset_edgeSet he
    have h : (e = s(0, 1) ∨ e = s(0, 2) ∨ e = s(0, 3)) ∧ ¬ e.IsDiag := by
      simpa [doubleStarLeftGraph] using hedge
    exact h.1
  have hle_edges : p.edges.length ≤ 3 := doubleStarLeft_sym2_edges_length_le_three htrail.edges_nodup hsub
  simpa [SimpleGraph.Walk.length_edges] using hle_edges

theorem doubleStarLeftGraph_isAcyclic : doubleStarLeftGraph.IsAcyclic := by
  intro v c hc
  have hle : c.length ≤ 3 := doubleStarLeft_edges_length_le_three c hc.isTrail
  have hge : 3 ≤ c.length := hc.three_le_length
  have hlen : c.length = 3 := by omega
  cases c with
  | nil => simp at hlen
  | cons h1 c1 =>
      cases c1 with
      | nil => simp at hlen
      | cons h2 c2 =>
          cases c2 with
          | nil => simp at hlen
          | cons h3 c3 =>
              cases c3 with
              | nil =>
                  exact doubleStarLeft_no_triangle ⟨h1, h2, h3⟩
              | cons h4 c4 =>
                  simp at hlen

private theorem doubleStarRight_sym2_edges_length_le_three {l : List (Sym2 (Fin 8))}
    (hnodup : l.Nodup)
    (hmem : ∀ e ∈ l, e = s(4, 5) ∨ e = s(4, 6) ∨ e = s(4, 7)) :
    l.length ≤ 3 := by
  have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnodup
  rw [← hcard]
  have hsubset : l.toFinset ⊆ ({s(4, 5), s(4, 6), s(4, 7)} : Finset (Sym2 (Fin 8))) := by
    intro e he
    rcases List.mem_toFinset.mp he with he'
    rcases hmem e he' with rfl | rfl | rfl <;> simp
  have hcard_le := Finset.card_le_card hsubset
  simpa using hcard_le

def doubleStarRightGraph : SimpleGraph (Fin 8) :=
  SimpleGraph.fromEdgeSet ({s(4, 5), s(4, 6), s(4, 7)} : Set (Sym2 (Fin 8)))

theorem doubleStarRight_adj_iff (u v : Fin 8) :
    doubleStarRightGraph.Adj u v ↔
      (u = 4 ∧ (v = 5 ∨ v = 6 ∨ v = 7)) ∨
        (v = 4 ∧ (u = 5 ∨ u = 6 ∨ u = 7)) := by
  fin_cases u <;> fin_cases v <;> simp [doubleStarRightGraph]

theorem doubleStarRight_adj_left_eq_four_or_right_eq_four {u v : Fin 8}
    (h : doubleStarRightGraph.Adj u v) :
    u = 4 ∨ v = 4 := by
  rcases (doubleStarRight_adj_iff u v).1 h with h' | h'
  · exact Or.inl h'.1
  · exact Or.inr h'.1

theorem doubleStarRight_adj_right_eq_four_of_left_ne_four {u v : Fin 8}
    (hu : u ≠ 4) (h : doubleStarRightGraph.Adj u v) :
    v = 4 := by
  rcases doubleStarRight_adj_left_eq_four_or_right_eq_four h with h4 | h4
  · exact False.elim (hu h4)
  · exact h4

theorem doubleStarRight_adj_left_eq_four_of_right_ne_four {u v : Fin 8}
    (hv : v ≠ 4) (h : doubleStarRightGraph.Adj u v) :
    u = 4 := by
  rcases (doubleStarRight_adj_iff u v).1 h with h' | h'
  · exact h'.1
  · exact False.elim (hv h'.1)

theorem doubleStarRight_no_triangle {a b c : Fin 8} :
    ¬ (doubleStarRightGraph.Adj a b ∧ doubleStarRightGraph.Adj b c ∧ doubleStarRightGraph.Adj c a) := by
  rintro ⟨hab, hbc, hca⟩
  by_cases ha : a = 4
  · subst a
    have hc_ne : c ≠ 4 := by
      intro hc
      subst hc
      exact hca.ne rfl
    have hb4 : b = 4 := doubleStarRight_adj_left_eq_four_of_right_ne_four hc_ne hbc
    subst b
    exact hab.ne rfl
  · have hb4 : b = 4 := doubleStarRight_adj_right_eq_four_of_left_ne_four ha hab
    have hc4 : c = 4 := doubleStarRight_adj_left_eq_four_of_right_ne_four ha hca
    subst b
    subst c
    exact hbc.ne rfl

theorem doubleStarRight_edges_length_le_three {v w : Fin 8}
    (p : doubleStarRightGraph.Walk v w) (htrail : p.IsTrail) :
    p.length ≤ 3 := by
  have hsub : ∀ e ∈ p.edges, e = s(4, 5) ∨ e = s(4, 6) ∨ e = s(4, 7) := by
    intro e he
    have hedge : e ∈ doubleStarRightGraph.edgeSet := p.edges_subset_edgeSet he
    have h : (e = s(4, 5) ∨ e = s(4, 6) ∨ e = s(4, 7)) ∧ ¬ e.IsDiag := by
      simpa [doubleStarRightGraph] using hedge
    exact h.1
  have hle_edges : p.edges.length ≤ 3 :=
    doubleStarRight_sym2_edges_length_le_three htrail.edges_nodup hsub
  simpa [SimpleGraph.Walk.length_edges] using hle_edges

theorem doubleStarRightGraph_isAcyclic : doubleStarRightGraph.IsAcyclic := by
  intro v c hc
  have hle : c.length ≤ 3 := doubleStarRight_edges_length_le_three c hc.isTrail
  have hge : 3 ≤ c.length := hc.three_le_length
  have hlen : c.length = 3 := by omega
  cases c with
  | nil => simp at hlen
  | cons h1 c1 =>
      cases c1 with
      | nil => simp at hlen
      | cons h2 c2 =>
          cases c2 with
          | nil => simp at hlen
          | cons h3 c3 =>
              cases c3 with
              | nil =>
                  exact doubleStarRight_no_triangle ⟨h1, h2, h3⟩
              | cons h4 c4 =>
                  simp at hlen

def doubleStarIsLeft (v : Fin 8) : Prop := v.1 < 4

def doubleStarIsRight (v : Fin 8) : Prop := 4 ≤ v.1

theorem doubleStar_adj_left_iff {u v : Fin 8} (h : doubleStarGraph.Adj u v) :
    doubleStarIsLeft u ↔ doubleStarIsLeft v := by
  fin_cases u <;> fin_cases v <;> simp [doubleStarGraph, doubleStarIsLeft] at h ⊢

theorem doubleStar_adj_right_iff {u v : Fin 8} (h : doubleStarGraph.Adj u v) :
    doubleStarIsRight u ↔ doubleStarIsRight v := by
  fin_cases u <;> fin_cases v <;> simp [doubleStarGraph, doubleStarIsRight] at h ⊢

theorem mem_doubleStarLeftGraph_edgeSet_of_adj_of_left {u v : Fin 8}
    (h : doubleStarGraph.Adj u v) (hu : doubleStarIsLeft u) :
    s(u, v) ∈ doubleStarLeftGraph.edgeSet := by
  fin_cases u <;> fin_cases v <;>
    simp [doubleStarGraph, doubleStarLeftGraph, doubleStarIsLeft] at h hu ⊢

theorem mem_doubleStarRightGraph_edgeSet_of_adj_of_right {u v : Fin 8}
    (h : doubleStarGraph.Adj u v) (hu : doubleStarIsRight u) :
    s(u, v) ∈ doubleStarRightGraph.edgeSet := by
  fin_cases u <;> fin_cases v <;>
    simp [doubleStarGraph, doubleStarRightGraph, doubleStarIsRight] at h hu ⊢

theorem doubleStar_walk_edges_subset_left {u v : Fin 8} (p : doubleStarGraph.Walk u v)
    (hu : doubleStarIsLeft u) :
    ∀ e, e ∈ p.edges → e ∈ doubleStarLeftGraph.edgeSet := by
  induction p with
  | nil =>
      intro e he
      simp at he
  | @cons u v w h p ih =>
      have hv : doubleStarIsLeft v := (doubleStar_adj_left_iff h).1 hu
      intro e he
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact mem_doubleStarLeftGraph_edgeSet_of_adj_of_left h hu
      · exact ih hv e he

theorem doubleStar_walk_edges_subset_right {u v : Fin 8} (p : doubleStarGraph.Walk u v)
    (hu : doubleStarIsRight u) :
    ∀ e, e ∈ p.edges → e ∈ doubleStarRightGraph.edgeSet := by
  induction p with
  | nil =>
      intro e he
      simp at he
  | @cons u v w h p ih =>
      have hv : doubleStarIsRight v := (doubleStar_adj_right_iff h).1 hu
      intro e he
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact mem_doubleStarRightGraph_edgeSet_of_adj_of_right h hu
      · exact ih hv e he

theorem doubleStarGraph_isAcyclic : doubleStarGraph.IsAcyclic := by
  intro v c hc
  by_cases hv : doubleStarIsLeft v
  · let cLeft := c.transfer doubleStarLeftGraph (doubleStar_walk_edges_subset_left c hv)
    have hcLeft : cLeft.IsCycle := Walk.IsCycle.transfer (qc := hc) _
    exact doubleStarLeftGraph_isAcyclic cLeft hcLeft
  · have hvRight : doubleStarIsRight v := by
      simpa [doubleStarIsRight, doubleStarIsLeft, Nat.not_lt] using hv
    let cRight := c.transfer doubleStarRightGraph (doubleStar_walk_edges_subset_right c hvRight)
    have hcRight : cRight.IsCycle := Walk.IsCycle.transfer (qc := hc) _
    exact doubleStarRightGraph_isAcyclic cRight hcRight

/-- Even on the explicit two-face annulus witness, honest facial closed walks remain impossible:
the left ambient face still has the three-star boundary, which admits no nonempty closed trail. -/
theorem not_nonempty_planarBoundaryClosedWalkEmbeddingData_doubleStarEmbedding :
    ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData doubleStarEmbedding) := by
  rintro ⟨geom⟩
  let data := geom.faceBoundaryClosedWalk doubleLeftFace
  have hleftEdges :
      ∀ e, e ∈ data.walk.edges → e ∈ doubleStarLeftGraph.edgeSet := by
    intro e he
    have hface : e ∈ (doubleStarEmbedding.faceBoundary doubleLeftFace.1).image Subtype.val :=
      data.hedge_sub e he
    have hedge : e = s(0, 1) ∨ e = s(0, 2) ∨ e = s(0, 3) := by
      simpa [doubleStarEmbedding, doubleStarFaceBoundary, doubleLeftFace, doubleLeftFaceIdx,
        ds01, ds02, ds03] using hface
    rcases hedge with rfl | rfl | rfl <;> simp [doubleStarLeftGraph]
  let leftWalk := data.walk.transfer doubleStarLeftGraph hleftEdges
  have htrail : leftWalk.IsTrail := by
    have hnodup : leftWalk.edges.Nodup := by
      simpa [leftWalk] using data.hnodup_edges
    simpa [SimpleGraph.Walk.isTrail_def] using hnodup
  have hpath : leftWalk.IsPath := (doubleStarLeftGraph_isAcyclic.isPath_iff_isTrail leftWalk).2 htrail
  have hnil : leftWalk = .nil := (SimpleGraph.Walk.isPath_iff_eq_nil leftWalk).1 hpath
  have hnonempty : 0 < leftWalk.length := by
    simpa [leftWalk] using data.hnonempty
  rw [hnil] at hnonempty
  simp at hnonempty

theorem not_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource_doubleStarEmbedding :
    ¬ Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource doubleStarEmbedding) := by
  rintro ⟨source⟩
  exact not_nonempty_planarBoundaryClosedWalkEmbeddingData_doubleStarEmbedding
    ⟨source.toPlanarBoundaryClosedWalkEmbeddingData⟩

theorem admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph :
    AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData doubleStarGraph := by
  exact ⟨doubleStarEmbedding,
    nonempty_planarBoundaryAnnulusBoundaryReachabilityData_doubleStarEmbedding⟩

theorem admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_doubleStarGraph :
    AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData doubleStarGraph := by
  exact ⟨doubleStarEmbedding,
    nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_doubleStarEmbedding⟩

theorem admitsPlanarBoundarySelectedBoundaryArcGeometry_doubleStarGraph :
    AdmitsPlanarBoundarySelectedBoundaryArcGeometry doubleStarGraph := by
  exact ⟨doubleStarEmbedding,
    nonempty_planarBoundarySelectedBoundaryArcGeometry_doubleStarEmbedding⟩

theorem not_admitsPlanarBoundaryClosedWalkEmbeddingData_doubleStarGraph :
    ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData doubleStarGraph := by
  exact
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      doubleStarGraph_isAcyclic ⟨ds01⟩

theorem not_nonempty_planarBoundaryDartCycleEmbeddingData_doubleStarEmbedding :
    ¬ Nonempty (PlanarBoundaryDartCycleEmbeddingData doubleStarEmbedding) := by
  exact
    not_nonempty_planarBoundaryDartCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      doubleStarGraph_isAcyclic ⟨ds01⟩

theorem not_nonempty_planarBoundaryPureDartCycleEmbeddingData_doubleStarEmbedding :
    ¬ Nonempty (PlanarBoundaryPureDartCycleEmbeddingData doubleStarEmbedding) := by
  exact
    not_nonempty_planarBoundaryPureDartCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      doubleStarGraph_isAcyclic ⟨ds01⟩

theorem not_nonempty_planarBoundaryDartSuccessorCycleEmbeddingData_doubleStarEmbedding :
    ¬ Nonempty (PlanarBoundaryDartSuccessorCycleEmbeddingData doubleStarEmbedding) := by
  exact
    not_nonempty_planarBoundaryDartSuccessorCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      doubleStarGraph_isAcyclic ⟨ds01⟩

theorem not_admitsPlanarBoundaryDartCycleEmbeddingData_doubleStarGraph :
    ¬ AdmitsPlanarBoundaryDartCycleEmbeddingData doubleStarGraph := by
  exact
    not_admitsPlanarBoundaryDartCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      doubleStarGraph_isAcyclic ⟨ds01⟩

theorem not_admitsPlanarBoundaryPureDartCycleEmbeddingData_doubleStarGraph :
    ¬ AdmitsPlanarBoundaryPureDartCycleEmbeddingData doubleStarGraph := by
  exact
    not_admitsPlanarBoundaryPureDartCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      doubleStarGraph_isAcyclic ⟨ds01⟩

theorem not_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_doubleStarGraph :
    ¬ AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData doubleStarGraph := by
  exact
    not_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      doubleStarGraph_isAcyclic ⟨ds01⟩

theorem not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_doubleStarGraph :
    ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource doubleStarGraph := by
  exact
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      doubleStarGraph_isAcyclic ⟨ds01⟩

theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_withoutClosedWalkAnnulusBoundarySource_doubleStarGraph :
    And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData doubleStarGraph)
      (AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData doubleStarGraph) ∧
        ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource doubleStarGraph := by
  exact
    Mettapedia.GraphTheory.FourColor.admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_withoutClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      doubleStarGraph_isAcyclic ⟨ds01⟩
      (And.intro
      admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
      admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_doubleStarGraph)

theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_withoutClosedWalkAnnulusBoundarySource_doubleStarGraph :
    And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData doubleStarGraph)
      (AdmitsPlanarBoundarySelectedBoundaryArcGeometry doubleStarGraph) ∧
        ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource doubleStarGraph := by
  exact
    Mettapedia.GraphTheory.FourColor.admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_withoutClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      doubleStarGraph_isAcyclic ⟨ds01⟩
      (And.intro
      admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
      admitsPlanarBoundarySelectedBoundaryArcGeometry_doubleStarGraph)

theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_withoutDartCycle_doubleStarGraph :
    And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData doubleStarGraph)
      (AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData doubleStarGraph) ∧
        ¬ AdmitsPlanarBoundaryDartCycleEmbeddingData doubleStarGraph := by
  exact ⟨
    And.intro admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
      admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_doubleStarGraph,
    not_admitsPlanarBoundaryDartCycleEmbeddingData_doubleStarGraph⟩

theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_withoutDartCycle_doubleStarGraph :
    And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData doubleStarGraph)
      (AdmitsPlanarBoundarySelectedBoundaryArcGeometry doubleStarGraph) ∧
        ¬ AdmitsPlanarBoundaryDartCycleEmbeddingData doubleStarGraph := by
  exact ⟨
    And.intro admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
      admitsPlanarBoundarySelectedBoundaryArcGeometry_doubleStarGraph,
    not_admitsPlanarBoundaryDartCycleEmbeddingData_doubleStarGraph⟩

theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_withoutPureDartCycle_doubleStarGraph :
    And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData doubleStarGraph)
      (AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData doubleStarGraph) ∧
        ¬ AdmitsPlanarBoundaryPureDartCycleEmbeddingData doubleStarGraph := by
  exact ⟨
    And.intro admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
      admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_doubleStarGraph,
    not_admitsPlanarBoundaryPureDartCycleEmbeddingData_doubleStarGraph⟩

theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_withoutPureDartCycle_doubleStarGraph :
    And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData doubleStarGraph)
      (AdmitsPlanarBoundarySelectedBoundaryArcGeometry doubleStarGraph) ∧
        ¬ AdmitsPlanarBoundaryPureDartCycleEmbeddingData doubleStarGraph := by
  exact ⟨
    And.intro admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
      admitsPlanarBoundarySelectedBoundaryArcGeometry_doubleStarGraph,
    not_admitsPlanarBoundaryPureDartCycleEmbeddingData_doubleStarGraph⟩

theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_withoutDartSuccessorCycle_doubleStarGraph :
    And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData doubleStarGraph)
      (AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData doubleStarGraph) ∧
        ¬ AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData doubleStarGraph := by
  exact ⟨
    And.intro admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
      admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_doubleStarGraph,
    not_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_doubleStarGraph⟩

theorem
    admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_withoutDartSuccessorCycle_doubleStarGraph :
    And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData doubleStarGraph)
      (AdmitsPlanarBoundarySelectedBoundaryArcGeometry doubleStarGraph) ∧
        ¬ AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData doubleStarGraph := by
  exact ⟨
    And.intro admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
      admitsPlanarBoundarySelectedBoundaryArcGeometry_doubleStarGraph,
    not_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_doubleStarGraph⟩

theorem exists_embedding_withPlanarBoundaryAnnulusBoundaryReachabilityData_andPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_withoutClosedWalkAnnulusBoundarySource :
    ∃ emb : PlaneEmbeddingWithBoundary doubleStarGraph,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          ¬ Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) := by
  exact ⟨doubleStarEmbedding,
    nonempty_planarBoundaryAnnulusBoundaryReachabilityData_doubleStarEmbedding,
    nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_doubleStarEmbedding,
    not_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource_doubleStarEmbedding⟩

theorem
    exists_embedding_withPlanarBoundaryAnnulusBoundaryReachabilityData_andPlanarBoundarySelectedBoundaryArcGeometry_withoutClosedWalkAnnulusBoundarySource :
    ∃ emb : PlaneEmbeddingWithBoundary doubleStarGraph,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          ¬ Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) := by
  exact ⟨doubleStarEmbedding,
    nonempty_planarBoundaryAnnulusBoundaryReachabilityData_doubleStarEmbedding,
    nonempty_planarBoundarySelectedBoundaryArcGeometry_doubleStarEmbedding,
    not_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource_doubleStarEmbedding⟩

theorem
    exists_embedding_withPlanarBoundaryAnnulusBoundaryReachabilityData_andPlanarBoundarySelectedBoundaryArcGeometry_withoutDartCycle :
    ∃ emb : PlaneEmbeddingWithBoundary doubleStarGraph,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          ¬ Nonempty (PlanarBoundaryDartCycleEmbeddingData emb) := by
  exact ⟨doubleStarEmbedding,
    nonempty_planarBoundaryAnnulusBoundaryReachabilityData_doubleStarEmbedding,
    nonempty_planarBoundarySelectedBoundaryArcGeometry_doubleStarEmbedding,
    not_nonempty_planarBoundaryDartCycleEmbeddingData_doubleStarEmbedding⟩

/-- There is no same-embedding derivation from annulus boundary reachability plus cyclic
selected-boundary face arcs to the honest closed-walk annulus source. The two-face double-star
embedding witnesses the gap directly. -/
theorem
    not_forall_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource_of_nonempty_planarBoundaryAnnulusBoundaryReachabilityData_and_nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary doubleStarGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) →
            Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) := by
  intro h
  exact not_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource_doubleStarEmbedding
    (h nonempty_planarBoundaryAnnulusBoundaryReachabilityData_doubleStarEmbedding
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_doubleStarEmbedding)

theorem
    not_forall_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource_of_nonempty_planarBoundaryAnnulusBoundaryReachabilityData_and_nonempty_planarBoundarySelectedBoundaryArcGeometry :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary doubleStarGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) →
            Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) := by
  intro h
  exact not_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource_doubleStarEmbedding
    (h nonempty_planarBoundaryAnnulusBoundaryReachabilityData_doubleStarEmbedding
      nonempty_planarBoundarySelectedBoundaryArcGeometry_doubleStarEmbedding)

theorem
    not_forall_nonempty_planarBoundaryDartCycleEmbeddingData_of_nonempty_planarBoundaryAnnulusBoundaryReachabilityData_and_nonempty_planarBoundarySelectedBoundaryArcGeometry :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary doubleStarGraph},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) →
            Nonempty (PlanarBoundaryDartCycleEmbeddingData emb) := by
  intro h
  exact not_nonempty_planarBoundaryDartCycleEmbeddingData_doubleStarEmbedding
    (h nonempty_planarBoundaryAnnulusBoundaryReachabilityData_doubleStarEmbedding
      nonempty_planarBoundarySelectedBoundaryArcGeometry_doubleStarEmbedding)

theorem
    not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData :
    ¬ ∀ G : SimpleGraph (Fin 8),
        And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
          (AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G) →
            AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  exact
    Mettapedia.GraphTheory.FourColor.not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_exists_isAcyclic_of_nonempty_edgeSet_and_admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData
      ⟨doubleStarGraph, doubleStarGraph_isAcyclic, ⟨ds01⟩,
        And.intro admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
          admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_doubleStarGraph⟩

theorem
    not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry :
    ¬ ∀ G : SimpleGraph (Fin 8),
        And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
          (AdmitsPlanarBoundarySelectedBoundaryArcGeometry G) →
            AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  exact
    Mettapedia.GraphTheory.FourColor.not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_exists_isAcyclic_of_nonempty_edgeSet_and_admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry
      ⟨doubleStarGraph, doubleStarGraph_isAcyclic, ⟨ds01⟩,
        And.intro admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
          admitsPlanarBoundarySelectedBoundaryArcGeometry_doubleStarGraph⟩

theorem
    not_forall_admitsPlanarBoundaryDartCycleEmbeddingData_of_admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData :
    ¬ ∀ G : SimpleGraph (Fin 8),
        And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
          (AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G) →
            AdmitsPlanarBoundaryDartCycleEmbeddingData G := by
  intro h
  exact not_admitsPlanarBoundaryDartCycleEmbeddingData_doubleStarGraph
    (h doubleStarGraph <|
      And.intro admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
        admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_doubleStarGraph)

theorem
    not_forall_admitsPlanarBoundaryDartCycleEmbeddingData_of_admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry :
    ¬ ∀ G : SimpleGraph (Fin 8),
        And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
          (AdmitsPlanarBoundarySelectedBoundaryArcGeometry G) →
            AdmitsPlanarBoundaryDartCycleEmbeddingData G := by
  intro h
  exact not_admitsPlanarBoundaryDartCycleEmbeddingData_doubleStarGraph
    (h doubleStarGraph <|
      And.intro admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
        admitsPlanarBoundarySelectedBoundaryArcGeometry_doubleStarGraph)

theorem
    not_forall_admitsPlanarBoundaryPureDartCycleEmbeddingData_of_admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry :
    ¬ ∀ G : SimpleGraph (Fin 8),
        And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
          (AdmitsPlanarBoundarySelectedBoundaryArcGeometry G) →
            AdmitsPlanarBoundaryPureDartCycleEmbeddingData G := by
  intro h
  exact not_admitsPlanarBoundaryPureDartCycleEmbeddingData_doubleStarGraph
    (h doubleStarGraph <|
      And.intro admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
        admitsPlanarBoundarySelectedBoundaryArcGeometry_doubleStarGraph)

theorem
    not_forall_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_of_admitsPlanarBoundaryAnnulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry :
    ¬ ∀ G : SimpleGraph (Fin 8),
        And (AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G)
          (AdmitsPlanarBoundarySelectedBoundaryArcGeometry G) →
            AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData G := by
  intro h
  exact not_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_doubleStarGraph
    (h doubleStarGraph <|
      And.intro admitsPlanarBoundaryAnnulusBoundaryReachabilityData_doubleStarGraph
        admitsPlanarBoundarySelectedBoundaryArcGeometry_doubleStarGraph)

/-- The current source ladder has two independent graph-level obstructions: the three-edge path
already shows the linear selected-boundary face-arc shell is weaker than honest facial walks, and
the three-star shows the same for the cyclic selected-boundary face-arc shell. -/
theorem exists_graphs_separating_linear_and_cyclic_selected_boundary_shells_from_closed_walk :
    ∃ Glin Gcyc : SimpleGraph (Fin 4),
      AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData Glin ∧
        ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData Glin ∧
        AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData Gcyc ∧
        ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData Gcyc := by
  exact ⟨pathGraph, starGraph,
    admitsPlanarBoundaryOrderedFaceArcEmbeddingData_pathGraph,
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_pathGraph,
    admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph,
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_starGraph⟩

/-- There is no generic derivation theorem from the current cyclic selected-boundary shell to the
honest facial closed-walk source. The one-face three-star is a concrete counterexample. -/
theorem not_forall_admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData :
    ¬ ∀ G : SimpleGraph (Fin 4),
        AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G →
          AdmitsPlanarBoundaryClosedWalkEmbeddingData G := by
  exact
    Mettapedia.GraphTheory.FourColor.not_forall_admitsPlanarBoundaryClosedWalkEmbeddingData_of_exists_isAcyclic_of_nonempty_edgeSet_and_property
      (fun G : SimpleGraph (Fin 4) => AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G)
      ⟨starGraph, starGraph_isAcyclic, ⟨s01⟩,
        admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph⟩

/-- There is no generic derivation theorem from the current cyclic selected-boundary shell to the
realized facial dart-cycle source. -/
theorem not_forall_admitsPlanarBoundaryDartCycleEmbeddingData_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData :
    ¬ ∀ G : SimpleGraph (Fin 4),
        AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G →
          AdmitsPlanarBoundaryDartCycleEmbeddingData G := by
  intro h
  exact not_admitsPlanarBoundaryDartCycleEmbeddingData_starGraph
    (h starGraph admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph)

/-- There is no generic derivation theorem from the current cyclic selected-boundary shell to the
pure facial dart-cycle source. -/
theorem not_forall_admitsPlanarBoundaryPureDartCycleEmbeddingData_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData :
    ¬ ∀ G : SimpleGraph (Fin 4),
        AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G →
          AdmitsPlanarBoundaryPureDartCycleEmbeddingData G := by
  intro h
  exact not_admitsPlanarBoundaryPureDartCycleEmbeddingData_starGraph
    (h starGraph admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph)

/-- There is no generic derivation theorem from the current cyclic selected-boundary shell to the
successor-based facial dart-cycle source. -/
theorem not_forall_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData :
    ¬ ∀ G : SimpleGraph (Fin 4),
        AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G →
          AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData G := by
  intro h
  exact not_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_starGraph
    (h starGraph admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph)

/-- There is likewise no generic derivation from the current cyclic selected-boundary shell to the
stronger closed-walk annulus-boundary source. -/
theorem
    not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData :
    ¬ ∀ G : SimpleGraph (Fin 4),
        AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G →
          AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  exact
    Mettapedia.GraphTheory.FourColor.not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_exists_isAcyclic_of_nonempty_edgeSet_and_property
      (fun G : SimpleGraph (Fin 4) => AdmitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData G)
      ⟨starGraph, starGraph_isAcyclic, ⟨s01⟩,
        admitsPlanarBoundaryCyclicOrderedFaceArcEmbeddingData_starGraph⟩

/-- The weaker bundled selected-boundary arc geometry shell also cannot generically imply the
honest facial closed-walk source. -/
theorem not_forall_admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundarySelectedBoundaryArcGeometry :
    ¬ ∀ G : SimpleGraph (Fin 4),
        AdmitsPlanarBoundarySelectedBoundaryArcGeometry G →
          AdmitsPlanarBoundaryClosedWalkEmbeddingData G := by
  exact
    Mettapedia.GraphTheory.FourColor.not_forall_admitsPlanarBoundaryClosedWalkEmbeddingData_of_exists_isAcyclic_of_nonempty_edgeSet_and_property
      (fun G : SimpleGraph (Fin 4) => AdmitsPlanarBoundarySelectedBoundaryArcGeometry G)
      ⟨starGraph, starGraph_isAcyclic, ⟨s01⟩,
        admitsPlanarBoundarySelectedBoundaryArcGeometry_starGraph⟩

/-- The weaker bundled selected-boundary arc geometry shell also cannot imply the closed-walk
annulus-boundary source. -/
theorem
    not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_admitsPlanarBoundarySelectedBoundaryArcGeometry :
    ¬ ∀ G : SimpleGraph (Fin 4),
        AdmitsPlanarBoundarySelectedBoundaryArcGeometry G →
          AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  exact
    Mettapedia.GraphTheory.FourColor.not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_exists_isAcyclic_of_nonempty_edgeSet_and_property
      (fun G : SimpleGraph (Fin 4) => AdmitsPlanarBoundarySelectedBoundaryArcGeometry G)
      ⟨starGraph, starGraph_isAcyclic, ⟨s01⟩,
        admitsPlanarBoundarySelectedBoundaryArcGeometry_starGraph⟩

/-- Even the split cyclic edge/vertex-walk-plus-selected-arc shell is still too weak to recover
an honest facial closed walk on the current weak embedding API. -/
theorem
    not_forall_admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace :
    ¬ ∀ G : SimpleGraph (Fin 4),
        AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace G →
          AdmitsPlanarBoundaryClosedWalkEmbeddingData G := by
  exact
    Mettapedia.GraphTheory.FourColor.not_forall_admitsPlanarBoundaryClosedWalkEmbeddingData_of_exists_isAcyclic_of_nonempty_edgeSet_and_property
      (fun G : SimpleGraph (Fin 4) =>
        AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace G)
      ⟨starGraph, starGraph_isAcyclic, ⟨s01⟩,
        admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace_starGraph⟩

/-- Even the split cyclic edge/vertex-walk-plus-selected-arc shell is too weak to recover the
closed-walk annulus-boundary source. -/
theorem
    not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace :
    ¬ ∀ G : SimpleGraph (Fin 4),
        AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace G →
          AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  exact
    Mettapedia.GraphTheory.FourColor.not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_exists_isAcyclic_of_nonempty_edgeSet_and_property
      (fun G : SimpleGraph (Fin 4) =>
        AdmitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace G)
      ⟨starGraph, starGraph_isAcyclic, ⟨s01⟩,
        admitsPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometryAndSelectedBoundaryArcOnFace_starGraph⟩

/-- There is no generic derivation theorem from the current linear selected-boundary face-arc
shell to the honest facial closed-walk source either: the one-face three-path already witnesses
the gap. -/
theorem not_forall_admitsPlanarBoundaryClosedWalkEmbeddingData_of_admitsPlanarBoundaryOrderedFaceArcEmbeddingData :
    ¬ ∀ G : SimpleGraph (Fin 4),
        AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G →
          AdmitsPlanarBoundaryClosedWalkEmbeddingData G := by
  exact
    Mettapedia.GraphTheory.FourColor.not_forall_admitsPlanarBoundaryClosedWalkEmbeddingData_of_exists_isAcyclic_of_nonempty_edgeSet_and_property
      (fun G : SimpleGraph (Fin 4) => AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G)
      ⟨pathGraph, pathGraph_isAcyclic, ⟨p01⟩,
        admitsPlanarBoundaryOrderedFaceArcEmbeddingData_pathGraph⟩

/-- The linear selected-boundary face-arc shell also cannot generically imply the stronger
closed-walk annulus-boundary source. -/
theorem
    not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_admitsPlanarBoundaryOrderedFaceArcEmbeddingData :
    ¬ ∀ G : SimpleGraph (Fin 4),
        AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G →
          AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource G := by
  exact
    Mettapedia.GraphTheory.FourColor.not_forall_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_exists_isAcyclic_of_nonempty_edgeSet_and_property
      (fun G : SimpleGraph (Fin 4) => AdmitsPlanarBoundaryOrderedFaceArcEmbeddingData G)
      ⟨pathGraph, pathGraph_isAcyclic, ⟨p01⟩,
        admitsPlanarBoundaryOrderedFaceArcEmbeddingData_pathGraph⟩

end PlanarBoundaryFaceBoundaryRunRegression

end

end Mettapedia.GraphTheory.FourColor
