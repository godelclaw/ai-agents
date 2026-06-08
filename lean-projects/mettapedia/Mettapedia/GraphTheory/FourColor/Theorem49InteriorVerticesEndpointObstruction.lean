import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVerticesAnnulusConstruction
import Mettapedia.GraphTheory.FourColor.Theorem49Synthesis
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusConstruction
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.FacialCyclePlanarEmbeddingWithBoundary
import Mettapedia.GraphTheory.OrderedPlanarEmbeddingWithBoundary
import Mettapedia.GraphTheory.WalkPlanarEmbeddingWithBoundary
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49InteriorVerticesEndpointObstruction

/-- A two-edge path graph used to isolate the endpoint-level obstruction in the
interior-vertex route. -/
def sharedEndpointGraph : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet ({s(0, 1), s(1, 2)} : Set (Sym2 (Fin 3)))

def eb01 : sharedEndpointGraph.edgeSet := ⟨s(0, 1), by simp [sharedEndpointGraph]⟩

def ei12 : sharedEndpointGraph.edgeSet := ⟨s(1, 2), by simp [sharedEndpointGraph]⟩

theorem eb01_ne_ei12 : eb01 ≠ ei12 := by
  intro h
  have := congrArg Subtype.val h
  simp [eb01, ei12] at this

theorem edge_eq_eb01_or_ei12 (e : sharedEndpointGraph.edgeSet) : e = eb01 ∨ e = ei12 := by
  have h : (e.1 = s(0, 1) ∨ e.1 = s(1, 2)) ∧ ¬ e.1.IsDiag := by
    simpa [sharedEndpointGraph] using e.2
  rcases h.1 with h01 | h12
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr (Subtype.ext h12)

abbrev SharedFace := Fin 2

def sharedFaces : Finset SharedFace := Finset.univ

def sharedFaceBoundary : SharedFace → Finset sharedEndpointGraph.edgeSet
  | ⟨0, _⟩ => {eb01, ei12}
  | ⟨1, _⟩ => {ei12}

theorem totalIncidenceCount_eb01 :
    totalIncidenceCount sharedFaceBoundary sharedFaces eb01 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      sharedFaces.filter (fun f => eb01 ∈ sharedFaceBoundary f) = {(0 : SharedFace)} := by
    ext f
    fin_cases f <;> simp [sharedFaces, sharedFaceBoundary, eb01_ne_ei12]
  rw [hfilter]
  simp

theorem totalIncidenceCount_ei12 :
    totalIncidenceCount sharedFaceBoundary sharedFaces ei12 = 2 := by
  unfold totalIncidenceCount
  have hfilter :
      sharedFaces.filter (fun f => ei12 ∈ sharedFaceBoundary f) = sharedFaces := by
    ext f
    fin_cases f <;> simp [sharedFaces, sharedFaceBoundary]
  rw [hfilter]
  simp [sharedFaces]

/-- A weak boundary-aware embedding whose face-incidence data makes `eb01` a selected-boundary
edge and `ei12` an interior edge.  The edges share vertex `1`, so edge-level disjointness is not
enough for the raw interior-endpoint carrier. -/
def sharedEndpointEmbedding : PlaneEmbeddingWithBoundary sharedEndpointGraph where
  Face := SharedFace
  faceDecidableEq := inferInstance
  faces := sharedFaces
  faceBoundary := sharedFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases edge_eq_eb01_or_ei12 e with rfl | rfl <;>
      simp [sharedFaces, sharedFaceBoundary]
  edge_one_or_two_faces := by
    intro e _he
    rcases edge_eq_eb01_or_ei12 e with rfl | rfl
    · left
      exact totalIncidenceCount_eb01
    · right
      exact totalIncidenceCount_ei12

def sharedFaceOne : {f // f ∈ sharedEndpointEmbedding.faces} :=
  ⟨(1 : SharedFace), by simp [sharedEndpointEmbedding, sharedFaces]⟩

theorem eb01_mem_selectedBoundarySupport :
    eb01 ∈ selectedBoundarySupport
      sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
      sharedEndpointEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by simp [sharedEndpointEmbedding, sharedFaces, sharedFaceBoundary],
    totalIncidenceCount_eb01⟩

theorem ei12_mem_interiorEdgeSupport :
    ei12 ∈ interiorEdgeSupport sharedEndpointEmbedding.faceBoundary
      sharedEndpointEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by simp [sharedEndpointEmbedding, sharedFaces, sharedFaceBoundary],
    totalIncidenceCount_ei12⟩

theorem vertex_one_mem_eb01 : (1 : Fin 3) ∈ (eb01 : Sym2 (Fin 3)) := by
  simp [eb01]

theorem vertex_one_mem_ei12 : (1 : Fin 3) ∈ (ei12 : Sym2 (Fin 3)) := by
  simp [ei12]

theorem planarEmbeddingBoundaryEdgeEndpointAdj_eb01_ei12 :
    planarEmbeddingBoundaryEdgeEndpointAdj eb01 ei12 := by
  exact ⟨eb01_ne_ei12, 1, vertex_one_mem_eb01, vertex_one_mem_ei12⟩

/-- The same weak incidence model still has a linear endpoint-sharing order on every face
boundary.  Thus linear boundary-order data alone cannot prove the raw endpoint-support
separation needed below. -/
def sharedEndpointOrderedFaceBoundaryData :
    PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData sharedEndpointEmbedding where
  faceBoundaryOrder := fun f => if f.1 = (0 : SharedFace) then [eb01, ei12] else [ei12]
  hchain := by
    intro f
    by_cases hf : f.1 = (0 : SharedFace)
    · simp [hf, planarEmbeddingBoundaryEdgeEndpointAdj_eb01_ei12]
    · simp [hf]
  hnodup := by
    intro f
    by_cases hf : f.1 = (0 : SharedFace)
    · simp [hf, eb01_ne_ei12]
    · simp [hf]
  hmem := by
    intro f e
    rcases f with ⟨f, hfmem⟩
    change SharedFace at f
    fin_cases f <;>
      rcases edge_eq_eb01_or_ei12 e with rfl | rfl <;>
        simp [sharedEndpointEmbedding, sharedFaces, sharedFaceBoundary, eb01_ne_ei12]

theorem nonempty_orderedFaceBoundaryData_sharedEndpoint :
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData sharedEndpointEmbedding) :=
  ⟨sharedEndpointOrderedFaceBoundaryData⟩

theorem nonempty_faceBoundaryRunGeometry_sharedEndpoint :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry sharedEndpointEmbedding) :=
  ⟨sharedEndpointOrderedFaceBoundaryData.toFaceBoundaryRunGeometry⟩

theorem sharedFaceOne_faceBoundaryOrder_eq_singleton
    (data : PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData sharedEndpointEmbedding) :
    data.faceBoundaryOrder sharedFaceOne = [ei12] := by
  generalize hrun : data.faceBoundaryOrder sharedFaceOne = run
  have hmem_i : ei12 ∈ run := by
    simpa [hrun] using
      (data.hmem sharedFaceOne ei12).2
        (by simp [sharedEndpointEmbedding, sharedFaceOne, sharedFaceBoundary])
  have hnodup : run.Nodup := by
    simpa [hrun] using data.hnodup sharedFaceOne
  have hsubset : ∀ e ∈ run, e = ei12 := by
    intro e he
    have hface : e ∈ sharedEndpointEmbedding.faceBoundary sharedFaceOne.1 := by
      exact (data.hmem sharedFaceOne e).1 (by simpa [hrun] using he)
    rcases edge_eq_eb01_or_ei12 e with rfl | rfl
    · exfalso
      simp [sharedEndpointEmbedding, sharedFaceOne, sharedFaceBoundary, eb01_ne_ei12] at hface
    · rfl
  cases run with
  | nil =>
      cases hmem_i
  | cons a tl =>
      have ha : a = ei12 := hsubset a (by simp)
      subst a
      have hnotmem : ei12 ∉ tl := (List.nodup_cons.mp hnodup).1
      have htl : tl = [] := by
        apply List.eq_nil_iff_forall_not_mem.2
        intro e he
        exact hnotmem ((hsubset e (by simp [he])) ▸ he)
      simp [htl]

theorem not_planarEmbeddingBoundaryEdgeEndpointAdj_ei12_self :
    ¬ planarEmbeddingBoundaryEdgeEndpointAdj ei12 ei12 := by
  intro h
  exact h.1 rfl

theorem not_nonempty_cyclicOrderedFaceBoundaryData_sharedEndpoint :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData sharedEndpointEmbedding) := by
  rintro ⟨data⟩
  have hrun : data.faceBoundaryOrder sharedFaceOne = [ei12] :=
    sharedFaceOne_faceBoundaryOrder_eq_singleton data.toOrderedFaceBoundaryData
  have hwrap : planarEmbeddingBoundaryEdgeEndpointAdj ei12 ei12 :=
    data.hwrap sharedFaceOne ei12 ei12 (by simp [hrun]) (by simp [hrun])
  exact not_planarEmbeddingBoundaryEdgeEndpointAdj_ei12_self hwrap

theorem not_nonempty_faceBoundaryClosedRunGeometry_sharedEndpoint :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry sharedEndpointEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedRunGeometry]
  exact not_nonempty_cyclicOrderedFaceBoundaryData_sharedEndpoint

theorem not_nonempty_faceBoundaryClosedVertexWalkGeometry_sharedEndpoint :
    ¬ Nonempty
      (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry sharedEndpointEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry]
  exact not_nonempty_cyclicOrderedFaceBoundaryData_sharedEndpoint

theorem not_nonempty_faceBoundaryClosedWalkGeometry_sharedEndpoint :
    ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry sharedEndpointEmbedding) := by
  intro h
  exact not_nonempty_cyclicOrderedFaceBoundaryData_sharedEndpoint
    (nonempty_faceBoundaryClosedWalkGeometry_implies_nonempty_cyclicOrderedFaceBoundaryData h)

/-- The edge supports are disjoint for the usual incidence-count reason. -/
theorem selectedBoundarySupport_disjoint_interiorEdgeSupport_sharedEndpoint :
    Disjoint
      (selectedBoundarySupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
        sharedEndpointEmbedding.faces)
      (interiorEdgeSupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces) :=
  selectedBoundarySupport_disjoint_interiorEdgeSupport
    sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces

/-- Nevertheless, a selected-boundary edge and an interior edge can share a primal endpoint. -/
theorem exists_selectedBoundarySupport_interiorEdgeSupport_shared_endpoint :
    ∃ v : Fin 3, ∃ eInterior eBoundary : sharedEndpointGraph.edgeSet,
      eInterior ∈ interiorEdgeSupport sharedEndpointEmbedding.faceBoundary
        sharedEndpointEmbedding.faces ∧
      eBoundary ∈ selectedBoundarySupport sharedEndpointEmbedding.faceBoundary
        sharedEndpointEmbedding.faces sharedEndpointEmbedding.faces ∧
      v ∈ (eInterior : Sym2 (Fin 3)) ∧
      v ∈ (eBoundary : Sym2 (Fin 3)) :=
  ⟨1, ei12, eb01, ei12_mem_interiorEdgeSupport, eb01_mem_selectedBoundarySupport,
    vertex_one_mem_ei12, vertex_one_mem_eb01⟩

/-- The endpoint-support version of the obstruction: the finite vertex endpoint supports are not
disjoint even though the corresponding edge supports are disjoint. -/
theorem not_endpointSupport_disjoint_sharedEndpoint :
    ¬ Disjoint (interiorEdgeEndpointSupport sharedEndpointEmbedding)
      (edgeEndpointSupport
        (selectedBoundarySupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
          sharedEndpointEmbedding.faces)) := by
  intro hdisj
  have hNoEndpoint :
      ∀ v : Fin 3,
        (∃ e ∈ interiorEdgeSupport sharedEndpointEmbedding.faceBoundary
          sharedEndpointEmbedding.faces, v ∈ (e : Sym2 (Fin 3))) →
          ∀ e ∈ selectedBoundarySupport sharedEndpointEmbedding.faceBoundary
            sharedEndpointEmbedding.faces sharedEndpointEmbedding.faces,
            v ∉ (e : Sym2 (Fin 3)) := by
    exact
      (edgeEndpointSupport_disjoint_iff_no_shared_endpoint
        (interiorEdgeSupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces)
        (selectedBoundarySupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
          sharedEndpointEmbedding.faces)).1
        (by simpa [interiorEdgeEndpointSupport] using hdisj)
  exact hNoEndpoint 1 ⟨ei12, ei12_mem_interiorEdgeSupport, vertex_one_mem_ei12⟩
    eb01 eb01_mem_selectedBoundarySupport vertex_one_mem_eb01

/-- Linear endpoint-sharing face-boundary order is still insufficient for the raw endpoint route:
the countermodel admits such ordered runs while failing endpoint-support disjointness. -/
theorem orderedFaceBoundaryData_does_not_imply_endpointSupport_disjoint_sharedEndpoint :
    Nonempty (PlaneEmbeddingWithBoundary.OrderedFaceBoundaryData sharedEndpointEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport sharedEndpointEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
            sharedEndpointEmbedding.faces)) :=
  ⟨nonempty_orderedFaceBoundaryData_sharedEndpoint, not_endpointSupport_disjoint_sharedEndpoint⟩

/-- The shared-endpoint countermodel is a linear-run obstruction only: it refutes the linear
boundary-order shortcut, but the cyclic and honest closed-walk source layers reject it because the
one-edge interior face would have to close by making an edge adjacent to itself. -/
theorem linearRun_endpointSupport_obstruction_not_closedWalk_sharedEndpoint :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryRunGeometry sharedEndpointEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport sharedEndpointEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
            sharedEndpointEmbedding.faces)) ∧
      ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry sharedEndpointEmbedding) ∧
      ¬ Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry sharedEndpointEmbedding) :=
  ⟨nonempty_faceBoundaryRunGeometry_sharedEndpoint, not_endpointSupport_disjoint_sharedEndpoint,
    not_nonempty_faceBoundaryClosedRunGeometry_sharedEndpoint,
    not_nonempty_faceBoundaryClosedWalkGeometry_sharedEndpoint⟩

/-- This concrete model refutes the false shortcut from edge-level disjointness to the
endpoint-level separation needed for raw interior-edge endpoints. -/
theorem edge_disjointness_does_not_imply_endpoint_separation_sharedEndpoint :
    Disjoint
        (selectedBoundarySupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces
          sharedEndpointEmbedding.faces)
        (interiorEdgeSupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces) ∧
      ¬ (∀ v : Fin 3,
        (∃ e ∈ interiorEdgeSupport sharedEndpointEmbedding.faceBoundary sharedEndpointEmbedding.faces,
          v ∈ (e : Sym2 (Fin 3))) →
          ∀ e ∈ selectedBoundarySupport sharedEndpointEmbedding.faceBoundary
            sharedEndpointEmbedding.faces sharedEndpointEmbedding.faces,
            v ∉ (e : Sym2 (Fin 3))) := by
  constructor
  · exact selectedBoundarySupport_disjoint_interiorEdgeSupport_sharedEndpoint
  · intro hEndpoint
    exact hEndpoint 1 ⟨ei12, ei12_mem_interiorEdgeSupport, vertex_one_mem_ei12⟩
      eb01 eb01_mem_selectedBoundarySupport vertex_one_mem_eb01

/-- Consequently the raw interior-edge endpoint carrier is not already the purified carrier in
this model. -/
theorem selectedBoundaryInteriorEdgeEndpointVertices_ne_interiorEdgeEndpointSupport_sharedEndpoint :
    selectedBoundaryInteriorEdgeEndpointVertices sharedEndpointEmbedding ≠
      interiorEdgeEndpointSupport sharedEndpointEmbedding :=
  selectedBoundaryInteriorEdgeEndpointVertices_ne_interiorEdgeEndpointSupport_of_endpoint_shared
    (emb := sharedEndpointEmbedding) (v := (1 : Fin 3)) (eInterior := ei12)
    (eBoundary := eb01) ei12_mem_interiorEdgeSupport eb01_mem_selectedBoundarySupport
    vertex_one_mem_ei12 vertex_one_mem_eb01

/-- A two-triangle diamond used to test whether cyclic closed face-boundary runs are enough to
force the raw endpoint-separation side condition. -/
def diamondGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(0, 2), s(1, 3), s(2, 3)} : Set (Sym2 (Fin 4)))

def d01 : diamondGraph.edgeSet := ⟨s(0, 1), by simp [diamondGraph]⟩

def d12 : diamondGraph.edgeSet := ⟨s(1, 2), by simp [diamondGraph]⟩

def d02 : diamondGraph.edgeSet := ⟨s(0, 2), by simp [diamondGraph]⟩

def d13 : diamondGraph.edgeSet := ⟨s(1, 3), by simp [diamondGraph]⟩

def d23 : diamondGraph.edgeSet := ⟨s(2, 3), by simp [diamondGraph]⟩

theorem d01_ne_d12 : d01 ≠ d12 := by
  intro h
  have := congrArg Subtype.val h
  simp [d01, d12] at this

theorem d01_ne_d02 : d01 ≠ d02 := by
  intro h
  have := congrArg Subtype.val h
  simp [d01, d02] at this

theorem d12_ne_d02 : d12 ≠ d02 := by
  intro h
  have := congrArg Subtype.val h
  simp [d12, d02] at this

theorem d12_ne_d23 : d12 ≠ d23 := by
  intro h
  have := congrArg Subtype.val h
  simp [d12, d23] at this

theorem d12_ne_d13 : d12 ≠ d13 := by
  intro h
  have := congrArg Subtype.val h
  simp [d12, d13] at this

theorem d23_ne_d13 : d23 ≠ d13 := by
  intro h
  have := congrArg Subtype.val h
  simp [d23, d13] at this

theorem diamond_edge_eq
    (e : diamondGraph.edgeSet) :
    e = d01 ∨ e = d12 ∨ e = d02 ∨ e = d13 ∨ e = d23 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(0, 2) ∨ e.1 = s(1, 3) ∨
          e.1 = s(2, 3)) ∧
        ¬ e.1.IsDiag := by
    simpa [diamondGraph] using e.2
  rcases h.1 with h01 | h12 | h02 | h13 | h23
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr (Or.inl (Subtype.ext h12))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h02)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h13))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h23))))

abbrev DiamondFace := Fin 2

def diamondFaces : Finset DiamondFace := Finset.univ

def diamondFaceBoundary : DiamondFace → Finset diamondGraph.edgeSet
  | ⟨0, _⟩ => {d01, d12, d02}
  | ⟨1, _⟩ => {d12, d23, d13}

theorem totalIncidenceCount_d01 :
    totalIncidenceCount diamondFaceBoundary diamondFaces d01 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondFaces.filter (fun f => d01 ∈ diamondFaceBoundary f) = {(0 : DiamondFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_d12 :
    totalIncidenceCount diamondFaceBoundary diamondFaces d12 = 2 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondFaces.filter (fun f => d12 ∈ diamondFaceBoundary f) = diamondFaces := by
    ext f
    fin_cases f <;> simp [diamondFaces, diamondFaceBoundary]
  rw [hfilter]
  simp [diamondFaces]

theorem totalIncidenceCount_d02 :
    totalIncidenceCount diamondFaceBoundary diamondFaces d02 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondFaces.filter (fun f => d02 ∈ diamondFaceBoundary f) = {(0 : DiamondFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_d13 :
    totalIncidenceCount diamondFaceBoundary diamondFaces d13 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondFaces.filter (fun f => d13 ∈ diamondFaceBoundary f) = {(1 : DiamondFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_d23 :
    totalIncidenceCount diamondFaceBoundary diamondFaces d23 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondFaces.filter (fun f => d23 ∈ diamondFaceBoundary f) = {(1 : DiamondFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

/-- A weak incidence embedding of the two-triangle diamond.  The shared edge `d12` is an interior
edge, while `d01` is a selected-boundary edge sharing endpoint `1` with it. -/
def diamondEmbedding : PlaneEmbeddingWithBoundary diamondGraph where
  Face := DiamondFace
  faceDecidableEq := inferInstance
  faces := diamondFaces
  faceBoundary := diamondFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases diamond_edge_eq e with rfl | rfl | rfl | rfl | rfl <;>
      simp [diamondFaces, diamondFaceBoundary]
  edge_one_or_two_faces := by
    intro e _he
    rcases diamond_edge_eq e with rfl | rfl | rfl | rfl | rfl
    · left
      exact totalIncidenceCount_d01
    · right
      exact totalIncidenceCount_d12
    · left
      exact totalIncidenceCount_d02
    · left
      exact totalIncidenceCount_d13
    · left
      exact totalIncidenceCount_d23

theorem d01_mem_selectedBoundarySupport :
    d01 ∈ selectedBoundarySupport
      diamondEmbedding.faceBoundary diamondEmbedding.faces diamondEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by simp [diamondEmbedding, diamondFaces, diamondFaceBoundary],
    totalIncidenceCount_d01⟩

theorem d02_mem_selectedBoundarySupport :
    d02 ∈ selectedBoundarySupport
      diamondEmbedding.faceBoundary diamondEmbedding.faces diamondEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by simp [diamondEmbedding, diamondFaces, diamondFaceBoundary],
    totalIncidenceCount_d02⟩

theorem d13_mem_selectedBoundarySupport :
    d13 ∈ selectedBoundarySupport
      diamondEmbedding.faceBoundary diamondEmbedding.faces diamondEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by simp [diamondEmbedding, diamondFaces, diamondFaceBoundary],
    totalIncidenceCount_d13⟩

theorem d23_mem_selectedBoundarySupport :
    d23 ∈ selectedBoundarySupport
      diamondEmbedding.faceBoundary diamondEmbedding.faces diamondEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by simp [diamondEmbedding, diamondFaces, diamondFaceBoundary],
    totalIncidenceCount_d23⟩

theorem d12_mem_interiorEdgeSupport :
    d12 ∈ interiorEdgeSupport diamondEmbedding.faceBoundary diamondEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by simp [diamondEmbedding, diamondFaces, diamondFaceBoundary],
    totalIncidenceCount_d12⟩

theorem vertex_one_mem_d01 : (1 : Fin 4) ∈ (d01 : Sym2 (Fin 4)) := by
  simp [d01]

theorem vertex_one_mem_d12 : (1 : Fin 4) ∈ (d12 : Sym2 (Fin 4)) := by
  simp [d12]

theorem diamondAdj_d01_d12 : planarEmbeddingBoundaryEdgeEndpointAdj d01 d12 := by
  exact ⟨d01_ne_d12, 1, vertex_one_mem_d01, vertex_one_mem_d12⟩

theorem diamondAdj_d12_d02 : planarEmbeddingBoundaryEdgeEndpointAdj d12 d02 := by
  refine ⟨d12_ne_d02, 2, ?_, ?_⟩ <;> simp [d12, d02]

theorem diamondAdj_d02_d01 : planarEmbeddingBoundaryEdgeEndpointAdj d02 d01 := by
  refine ⟨d01_ne_d02.symm, 0, ?_, ?_⟩ <;> simp [d02, d01]

theorem diamondAdj_d12_d23 : planarEmbeddingBoundaryEdgeEndpointAdj d12 d23 := by
  refine ⟨d12_ne_d23, 2, ?_, ?_⟩ <;> simp [d12, d23]

theorem diamondAdj_d23_d13 : planarEmbeddingBoundaryEdgeEndpointAdj d23 d13 := by
  refine ⟨d23_ne_d13, 3, ?_, ?_⟩ <;> simp [d23, d13]

theorem diamondAdj_d13_d12 : planarEmbeddingBoundaryEdgeEndpointAdj d13 d12 := by
  refine ⟨d12_ne_d13.symm, 1, ?_, ?_⟩ <;> simp [d13, d12]

/-- The diamond has genuine cyclic closed face-boundary runs on both triangular faces. -/
def diamondCyclicOrderedFaceBoundaryData :
    PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData diamondEmbedding where
  faceBoundaryOrder := fun f =>
    if f.1 = (0 : DiamondFace) then [d01, d12, d02] else [d12, d23, d13]
  hchain := by
    intro f
    by_cases hf : f.1 = (0 : DiamondFace)
    · simp [hf, diamondAdj_d01_d12, diamondAdj_d12_d02]
    · simp [hf, diamondAdj_d12_d23, diamondAdj_d23_d13]
  hnodup := by
    intro f
    by_cases hf : f.1 = (0 : DiamondFace)
    · simp [hf, d01_ne_d12, d01_ne_d02, d12_ne_d02]
    · simp [hf, d12_ne_d23, d12_ne_d13, d23_ne_d13]
  hmem := by
    intro f e
    rcases f with ⟨f, hfmem⟩
    change DiamondFace at f
    fin_cases f <;>
      rcases diamond_edge_eq e with rfl | rfl | rfl | rfl | rfl <;>
        simp [diamondEmbedding, diamondFaces, diamondFaceBoundary,
          d01_ne_d12, d01_ne_d02, d12_ne_d02, d12_ne_d23, d12_ne_d13, d23_ne_d13]
  hwrap := by
    intro f first last hfirst hlast
    by_cases hf : f.1 = (0 : DiamondFace)
    · have hfirst' : first = d01 := by simpa [hf] using hfirst.symm
      have hlast' : last = d02 := by simpa [hf] using hlast.symm
      subst first
      subst last
      exact diamondAdj_d02_d01
    · have hfirst' : first = d12 := by simpa [hf] using hfirst.symm
      have hlast' : last = d13 := by simpa [hf] using hlast.symm
      subst first
      subst last
      exact diamondAdj_d13_d12

theorem nonempty_cyclicOrderedFaceBoundaryData_diamond :
    Nonempty (PlaneEmbeddingWithBoundary.CyclicOrderedFaceBoundaryData diamondEmbedding) :=
  ⟨diamondCyclicOrderedFaceBoundaryData⟩

theorem nonempty_faceBoundaryClosedRunGeometry_diamond :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry diamondEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedRunGeometry]
  exact nonempty_cyclicOrderedFaceBoundaryData_diamond

theorem nonempty_faceBoundaryClosedVertexWalkGeometry_diamond :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedVertexWalkGeometry diamondEmbedding) := by
  rw [← nonempty_cyclicOrderedFaceBoundaryData_iff_nonempty_faceBoundaryClosedVertexWalkGeometry]
  exact nonempty_cyclicOrderedFaceBoundaryData_diamond

def dart01 : diamondGraph.Dart := ⟨((0 : Fin 4), 1), by simp [diamondGraph]⟩

def dart12 : diamondGraph.Dart := ⟨((1 : Fin 4), 2), by simp [diamondGraph]⟩

def dart20 : diamondGraph.Dart := ⟨((2 : Fin 4), 0), by simp [diamondGraph]⟩

def dart23 : diamondGraph.Dart := ⟨((2 : Fin 4), 3), by simp [diamondGraph]⟩

def dart31 : diamondGraph.Dart := ⟨((3 : Fin 4), 1), by simp [diamondGraph]⟩

/-- The lower triangular face of the diamond as an honest oriented facial dart cycle. -/
def diamondFace0PureDartCycle
    (hf : (0 : DiamondFace) ∈ diamondEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle diamondEmbedding ⟨(0 : DiamondFace), hf⟩ where
  darts := [dart01, dart12, dart20]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dart01, dart12, dart20]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondEmbedding, diamondFaceBoundary, d01, d12, d02, dart01, dart12, dart20]
  hface_sub := by
    intro e he
    have he' : e = d01 ∨ e = d12 ∨ e = d02 := by
      simpa [diamondEmbedding, diamondFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [d01, d12, d02, dart01, dart12, dart20]

/-- The upper triangular face of the diamond as an honest oriented facial dart cycle. -/
def diamondFace1PureDartCycle
    (hf : (1 : DiamondFace) ∈ diamondEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle diamondEmbedding ⟨(1 : DiamondFace), hf⟩ where
  darts := [dart12, dart23, dart31]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dart12, dart23, dart31]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondEmbedding, diamondFaceBoundary, d12, d23, d13, dart12, dart23, dart31]
  hface_sub := by
    intro e he
    have he' : e = d12 ∨ e = d23 ∨ e = d13 := by
      simpa [diamondEmbedding, diamondFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [d12, d23, d13, dart12, dart23, dart31]

/-- The two-triangle diamond has actual facial dart cycles, hence actual facial closed walks. -/
def diamondFaceBoundaryPureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry diamondEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change DiamondFace at f
    by_cases h0 : f = (0 : DiamondFace)
    · subst f
      exact diamondFace0PureDartCycle hfmem
    · have h1 : f = (1 : DiamondFace) := by
        fin_cases f
        · exact False.elim (h0 rfl)
        · rfl
      subst f
      exact diamondFace1PureDartCycle hfmem

theorem nonempty_faceBoundaryClosedWalkGeometry_diamond :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry diamondEmbedding) :=
  ⟨diamondFaceBoundaryPureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry⟩

/-- A rotated lower-face dart cycle whose induced linear edge run begins with the two selected
boundary edges. This is used to show that selected-arc contiguity is still not enough to force
endpoint separation. -/
def diamondFace0SelectedArcPureDartCycle
    (hf : (0 : DiamondFace) ∈ diamondEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle diamondEmbedding ⟨(0 : DiamondFace), hf⟩ where
  darts := [dart20, dart01, dart12]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dart20, dart01, dart12]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondEmbedding, diamondFaceBoundary, d01, d12, d02, dart20, dart01, dart12]
  hface_sub := by
    intro e he
    have he' : e = d01 ∨ e = d12 ∨ e = d02 := by
      simpa [diamondEmbedding, diamondFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [d01, d12, d02, dart20, dart01, dart12]

/-- A rotated upper-face dart cycle whose induced linear edge run begins with the two selected
boundary edges. -/
def diamondFace1SelectedArcPureDartCycle
    (hf : (1 : DiamondFace) ∈ diamondEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle diamondEmbedding ⟨(1 : DiamondFace), hf⟩ where
  darts := [dart23, dart31, dart12]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dart23, dart31, dart12]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondEmbedding, diamondFaceBoundary, d12, d23, d13, dart23, dart31, dart12]
  hface_sub := by
    intro e he
    have he' : e = d12 ∨ e = d23 ∨ e = d13 := by
      simpa [diamondEmbedding, diamondFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [d12, d23, d13, dart23, dart31, dart12]

/-- The diamond also admits honest facial dart cycles whose induced linear runs make the selected
boundary edges contiguous on each triangular face. -/
def diamondSelectedArcPureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry diamondEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change DiamondFace at f
    by_cases h0 : f = (0 : DiamondFace)
    · subst f
      exact diamondFace0SelectedArcPureDartCycle hfmem
    · have h1 : f = (1 : DiamondFace) := by
        fin_cases f
        · exact False.elim (h0 rfl)
        · rfl
      subst f
      exact diamondFace1SelectedArcPureDartCycle hfmem

def diamondSelectedArcClosedWalkEmbeddingData :
    PlanarBoundaryClosedWalkEmbeddingData diamondEmbedding :=
  diamondSelectedArcPureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

theorem diamondSelectedArcClosedWalkEmbeddingData_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace diamondEmbedding.faces,
      (diamondSelectedArcClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f := by
  intro f
  let f0 : AmbientFace diamondEmbedding.faces :=
    ⟨(0 : DiamondFace), by simp [diamondEmbedding, diamondFaces]⟩
  let f1 : AmbientFace diamondEmbedding.faces :=
    ⟨(1 : DiamondFace), by simp [diamondEmbedding, diamondFaces]⟩
  have hf_cases : f = f0 ∨ f = f1 := by
    rcases f with ⟨⟨n, hn⟩, hfmem⟩
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · left
      exact Subtype.ext rfl
    · right
      exact Subtype.ext rfl
  rcases hf_cases with rfl | rfl
  · change
      (diamondSelectedArcClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f0
    refine ⟨[d02, d01], ?_, ?_⟩
    · decide
    · intro e
      rcases diamond_edge_eq e with rfl | rfl | rfl | rfl | rfl <;>
        decide
  · change
      (diamondSelectedArcClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f1
    refine ⟨[d23, d13], ?_, ?_⟩
    · decide
    · intro e
      rcases diamond_edge_eq e with rfl | rfl | rfl | rfl | rfl <;>
        decide

theorem nonempty_closedWalkEmbeddingDataAndSelectedBoundaryArcOnFace_diamond :
    ∃ geom : PlanarBoundaryClosedWalkEmbeddingData diamondEmbedding,
      ∀ f : AmbientFace diamondEmbedding.faces,
        (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f :=
  ⟨diamondSelectedArcClosedWalkEmbeddingData,
    diamondSelectedArcClosedWalkEmbeddingData_selectedBoundaryArcOnFace⟩

theorem not_endpointSupport_disjoint_diamond :
    ¬ Disjoint (interiorEdgeEndpointSupport diamondEmbedding)
      (edgeEndpointSupport
        (selectedBoundarySupport diamondEmbedding.faceBoundary diamondEmbedding.faces
          diamondEmbedding.faces)) := by
  intro hdisj
  have hNoEndpoint :
      ∀ v : Fin 4,
        (∃ e ∈ interiorEdgeSupport diamondEmbedding.faceBoundary
          diamondEmbedding.faces, v ∈ (e : Sym2 (Fin 4))) →
          ∀ e ∈ selectedBoundarySupport diamondEmbedding.faceBoundary
            diamondEmbedding.faces diamondEmbedding.faces,
            v ∉ (e : Sym2 (Fin 4)) := by
    exact
      (edgeEndpointSupport_disjoint_iff_no_shared_endpoint
        (interiorEdgeSupport diamondEmbedding.faceBoundary diamondEmbedding.faces)
        (selectedBoundarySupport diamondEmbedding.faceBoundary diamondEmbedding.faces
          diamondEmbedding.faces)).1
        (by simpa [interiorEdgeEndpointSupport] using hdisj)
  exact hNoEndpoint 1 ⟨d12, d12_mem_interiorEdgeSupport, vertex_one_mem_d12⟩
    d01 d01_mem_selectedBoundarySupport vertex_one_mem_d01

/-- Cyclic closed face-boundary runs alone still do not prove the raw endpoint-support separation
needed by the unpurified interior-edge endpoint carrier.  The two-triangle diamond has cyclic
closed runs, but its interior shared edge touches a selected-boundary edge at a primal endpoint. -/
theorem cyclicClosedRun_does_not_imply_endpointSupport_disjoint_diamond :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedRunGeometry diamondEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport diamondEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport diamondEmbedding.faceBoundary diamondEmbedding.faces
            diamondEmbedding.faces)) :=
  ⟨nonempty_faceBoundaryClosedRunGeometry_diamond, not_endpointSupport_disjoint_diamond⟩

/-- Even honest facial closed-walk geometry does not by itself prove the raw endpoint-support
separation needed by the unpurified interior-edge endpoint carrier.  The two-triangle diamond has
closed walks around both triangular faces, but its interior shared edge touches a selected-boundary
edge at a primal endpoint. -/
theorem faceBoundaryClosedWalkGeometry_does_not_imply_endpointSupport_disjoint_diamond :
    Nonempty (PlaneEmbeddingWithBoundary.FaceBoundaryClosedWalkGeometry diamondEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport diamondEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport diamondEmbedding.faceBoundary diamondEmbedding.faces
            diamondEmbedding.faces)) :=
  ⟨nonempty_faceBoundaryClosedWalkGeometry_diamond, not_endpointSupport_disjoint_diamond⟩

/-- Even honest facial closed walks whose induced linear runs make the selected-boundary edges a
contiguous arc on each face do not by themselves imply the endpoint-support separation needed by
the raw interior-edge endpoint carrier. The missing ingredient is still an annular no-touch
condition tying the chosen interior to the selected boundary. -/
theorem closedWalkSelectedArc_does_not_imply_endpointSupport_disjoint_diamond :
    (∃ geom : PlanarBoundaryClosedWalkEmbeddingData diamondEmbedding,
      ∀ f : AmbientFace diamondEmbedding.faces,
        (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport diamondEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport diamondEmbedding.faceBoundary diamondEmbedding.faces
            diamondEmbedding.faces)) :=
  ⟨nonempty_closedWalkEmbeddingDataAndSelectedBoundaryArcOnFace_diamond,
    not_endpointSupport_disjoint_diamond⟩

/-- A two-component boundary model: one component is the diamond carrying the raw endpoint
failure, and the second component is a separate triangular boundary component.  This lets the
model satisfy the two-root annulus boundary-source package while preserving the endpoint-support
obstruction. -/
def diamondWithTriangleGraph : SimpleGraph (Fin 7) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(0, 2), s(1, 3), s(2, 3),
        s(4, 5), s(5, 6), s(6, 4)} : Set (Sym2 (Fin 7)))

def dt01 : diamondWithTriangleGraph.edgeSet := ⟨s(0, 1), by simp [diamondWithTriangleGraph]⟩

def dt12 : diamondWithTriangleGraph.edgeSet := ⟨s(1, 2), by simp [diamondWithTriangleGraph]⟩

def dt02 : diamondWithTriangleGraph.edgeSet := ⟨s(0, 2), by simp [diamondWithTriangleGraph]⟩

def dt13 : diamondWithTriangleGraph.edgeSet := ⟨s(1, 3), by simp [diamondWithTriangleGraph]⟩

def dt23 : diamondWithTriangleGraph.edgeSet := ⟨s(2, 3), by simp [diamondWithTriangleGraph]⟩

def dt45 : diamondWithTriangleGraph.edgeSet := ⟨s(4, 5), by simp [diamondWithTriangleGraph]⟩

def dt56 : diamondWithTriangleGraph.edgeSet := ⟨s(5, 6), by simp [diamondWithTriangleGraph]⟩

def dt64 : diamondWithTriangleGraph.edgeSet := ⟨s(6, 4), by simp [diamondWithTriangleGraph]⟩

theorem diamondWithTriangle_edge_eq
    (e : diamondWithTriangleGraph.edgeSet) :
    e = dt01 ∨ e = dt12 ∨ e = dt02 ∨ e = dt13 ∨ e = dt23 ∨
      e = dt45 ∨ e = dt56 ∨ e = dt64 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(0, 2) ∨ e.1 = s(1, 3) ∨
          e.1 = s(2, 3) ∨ e.1 = s(4, 5) ∨ e.1 = s(5, 6) ∨ e.1 = s(6, 4)) ∧
        ¬ e.1.IsDiag := by
    simpa [diamondWithTriangleGraph] using e.2
  rcases h.1 with h01 | h12 | h02 | h13 | h23 | h45 | h56 | h64
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr (Or.inl (Subtype.ext h12))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h02)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h13))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h23)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h45))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h56)))))))
  · exact Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h64)))))))

abbrev DiamondWithTriangleFace := Fin 3

def diamondWithTriangleFaces : Finset DiamondWithTriangleFace := Finset.univ

def diamondWithTriangleFaceBoundary :
    DiamondWithTriangleFace → Finset diamondWithTriangleGraph.edgeSet
  | ⟨0, _⟩ => {dt02, dt01, dt12}
  | ⟨1, _⟩ => {dt23, dt13, dt12}
  | ⟨2, _⟩ => {dt45, dt56, dt64}

theorem totalIncidenceCount_dt01 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt01 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt01 ∈ diamondWithTriangleFaceBoundary f) =
        {(0 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt12 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt12 = 2 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt12 ∈ diamondWithTriangleFaceBoundary f) =
        ({(0 : DiamondWithTriangleFace), (1 : DiamondWithTriangleFace)} : Finset _) := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt02 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt02 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt02 ∈ diamondWithTriangleFaceBoundary f) =
        {(0 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt13 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt13 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt13 ∈ diamondWithTriangleFaceBoundary f) =
        {(1 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt23 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt23 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt23 ∈ diamondWithTriangleFaceBoundary f) =
        {(1 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt45 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt45 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt45 ∈ diamondWithTriangleFaceBoundary f) =
        {(2 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt56 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt56 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt56 ∈ diamondWithTriangleFaceBoundary f) =
        {(2 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_dt64 :
    totalIncidenceCount diamondWithTriangleFaceBoundary diamondWithTriangleFaces dt64 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      diamondWithTriangleFaces.filter
          (fun f => dt64 ∈ diamondWithTriangleFaceBoundary f) =
        {(2 : DiamondWithTriangleFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

def diamondWithTriangleEmbedding : PlaneEmbeddingWithBoundary diamondWithTriangleGraph where
  Face := DiamondWithTriangleFace
  faceDecidableEq := inferInstance
  faces := diamondWithTriangleFaces
  faceBoundary := diamondWithTriangleFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases diamondWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [Finset.mem_biUnion]
      exact ⟨(0 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(0 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(0 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(1 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(1 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(2 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(2 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(2 : DiamondWithTriangleFace), by exact Finset.mem_univ _, by decide⟩
  edge_one_or_two_faces := by
    intro e _he
    rcases diamondWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left
      exact totalIncidenceCount_dt01
    · right
      exact totalIncidenceCount_dt12
    · left
      exact totalIncidenceCount_dt02
    · left
      exact totalIncidenceCount_dt13
    · left
      exact totalIncidenceCount_dt23
    · left
      exact totalIncidenceCount_dt45
    · left
      exact totalIncidenceCount_dt56
    · left
      exact totalIncidenceCount_dt64

theorem dt01_mem_selectedBoundarySupport :
    dt01 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(0 : DiamondWithTriangleFace), by
        change (0 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt01⟩

theorem dt02_mem_selectedBoundarySupport :
    dt02 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(0 : DiamondWithTriangleFace), by
        change (0 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt02⟩

theorem dt13_mem_selectedBoundarySupport :
    dt13 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(1 : DiamondWithTriangleFace), by
        change (1 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt13⟩

theorem dt23_mem_selectedBoundarySupport :
    dt23 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(1 : DiamondWithTriangleFace), by
        change (1 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt23⟩

theorem dt45_mem_selectedBoundarySupport :
    dt45 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(2 : DiamondWithTriangleFace), by
        change (2 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt45⟩

theorem dt56_mem_selectedBoundarySupport :
    dt56 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(2 : DiamondWithTriangleFace), by
        change (2 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt56⟩

theorem dt64_mem_selectedBoundarySupport :
    dt64 ∈ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(2 : DiamondWithTriangleFace), by
        change (2 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt64⟩

theorem dt12_mem_interiorEdgeSupport :
    dt12 ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
      diamondWithTriangleEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(0 : DiamondWithTriangleFace), by
      change (0 : DiamondWithTriangleFace) ∈ diamondWithTriangleFaces
      exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_dt12⟩

theorem exists_selectedBoundarySupport_of_dt12_mem_faceBoundary_diamondWithTriangle
    {f : AmbientFace diamondWithTriangleEmbedding.faces}
    (hf12 : dt12 ∈ diamondWithTriangleEmbedding.faceBoundary f.1) :
    ∃ e ∈ diamondWithTriangleEmbedding.faceBoundary f.1,
      e ∈ selectedBoundarySupport
        diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
        diamondWithTriangleEmbedding.faces := by
  rcases f with ⟨f, _hf⟩
  change DiamondWithTriangleFace at f
  fin_cases f
  · exact ⟨dt01, by
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary],
      dt01_mem_selectedBoundarySupport⟩
  · exact ⟨dt13, by
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary],
      dt13_mem_selectedBoundarySupport⟩
  · have hnot :
        dt12 ∉ diamondWithTriangleEmbedding.faceBoundary (2 : DiamondWithTriangleFace) := by
      decide
    exact False.elim (hnot (by simpa using hf12))

theorem dt12_not_mem_selectedBoundarySupport :
    dt12 ∉ selectedBoundarySupport
      diamondWithTriangleEmbedding.faceBoundary diamondWithTriangleEmbedding.faces
      diamondWithTriangleEmbedding.faces := by
  intro h
  have hcount :
      totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
        diamondWithTriangleEmbedding.faces dt12 = 1 :=
    (mem_selectedBoundarySupport_iff diamondWithTriangleEmbedding.faceBoundary
      diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces).1 h |>.2
  simp [diamondWithTriangleEmbedding, totalIncidenceCount_dt12] at hcount

theorem vertex_one_mem_dt01 : (1 : Fin 7) ∈ (dt01 : Sym2 (Fin 7)) := by
  simp [dt01]

theorem vertex_one_mem_dt12 : (1 : Fin 7) ∈ (dt12 : Sym2 (Fin 7)) := by
  simp [dt12]

theorem not_endpointSupport_disjoint_diamondWithTriangle :
    ¬ Disjoint (interiorEdgeEndpointSupport diamondWithTriangleEmbedding)
      (edgeEndpointSupport
        (selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces)) := by
  intro hdisj
  have hNoEndpoint :
      ∀ v : Fin 7,
        (∃ e ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces, v ∈ (e : Sym2 (Fin 7))) →
          ∀ e ∈ selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces,
            v ∉ (e : Sym2 (Fin 7)) := by
    exact
      (edgeEndpointSupport_disjoint_iff_no_shared_endpoint
        (interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces)
        (selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces)).1
        (by simpa [interiorEdgeEndpointSupport] using hdisj)
  exact hNoEndpoint 1 ⟨dt12, dt12_mem_interiorEdgeSupport, vertex_one_mem_dt12⟩
    dt01 dt01_mem_selectedBoundarySupport vertex_one_mem_dt01

def dtDart01 : diamondWithTriangleGraph.Dart := ⟨((0 : Fin 7), 1), by
  simp [diamondWithTriangleGraph]⟩

def dtDart12 : diamondWithTriangleGraph.Dart := ⟨((1 : Fin 7), 2), by
  simp [diamondWithTriangleGraph]⟩

def dtDart20 : diamondWithTriangleGraph.Dart := ⟨((2 : Fin 7), 0), by
  simp [diamondWithTriangleGraph]⟩

def dtDart23 : diamondWithTriangleGraph.Dart := ⟨((2 : Fin 7), 3), by
  simp [diamondWithTriangleGraph]⟩

def dtDart31 : diamondWithTriangleGraph.Dart := ⟨((3 : Fin 7), 1), by
  simp [diamondWithTriangleGraph]⟩

def dtDart45 : diamondWithTriangleGraph.Dart := ⟨((4 : Fin 7), 5), by
  simp [diamondWithTriangleGraph]⟩

def dtDart56 : diamondWithTriangleGraph.Dart := ⟨((5 : Fin 7), 6), by
  simp [diamondWithTriangleGraph]⟩

def dtDart64 : diamondWithTriangleGraph.Dart := ⟨((6 : Fin 7), 4), by
  simp [diamondWithTriangleGraph]⟩

def diamondWithTriangleFace0SelectedArcPureDartCycle
    (hf : (0 : DiamondWithTriangleFace) ∈ diamondWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      diamondWithTriangleEmbedding ⟨(0 : DiamondWithTriangleFace), hf⟩ where
  darts := [dtDart20, dtDart01, dtDart12]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dtDart20, dtDart01, dtDart12]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary,
        dt02, dt01, dt12, dtDart20, dtDart01, dtDart12]
  hface_sub := by
    intro e he
    have he' : e = dt02 ∨ e = dt01 ∨ e = dt12 := by
      simpa [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [dt02, dt01, dt12, dtDart20, dtDart01, dtDart12]

def diamondWithTriangleFace1SelectedArcPureDartCycle
    (hf : (1 : DiamondWithTriangleFace) ∈ diamondWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      diamondWithTriangleEmbedding ⟨(1 : DiamondWithTriangleFace), hf⟩ where
  darts := [dtDart23, dtDart31, dtDart12]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dtDart23, dtDart31, dtDart12]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary,
        dt23, dt13, dt12, dtDart23, dtDart31, dtDart12]
  hface_sub := by
    intro e he
    have he' : e = dt23 ∨ e = dt13 ∨ e = dt12 := by
      simpa [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [dt23, dt13, dt12, dtDart23, dtDart31, dtDart12]

def diamondWithTriangleFace2PureDartCycle
    (hf : (2 : DiamondWithTriangleFace) ∈ diamondWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      diamondWithTriangleEmbedding ⟨(2 : DiamondWithTriangleFace), hf⟩ where
  darts := [dtDart45, dtDart56, dtDart64]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, dtDart45, dtDart56, dtDart64]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary,
        dt45, dt56, dt64, dtDart45, dtDart56, dtDart64]
  hface_sub := by
    intro e he
    have he' : e = dt45 ∨ e = dt56 ∨ e = dt64 := by
      simpa [diamondWithTriangleEmbedding, diamondWithTriangleFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [dt45, dt56, dt64, dtDart45, dtDart56, dtDart64]

def diamondWithTrianglePureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry diamondWithTriangleEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change DiamondWithTriangleFace at f
    by_cases h0 : f = (0 : DiamondWithTriangleFace)
    · subst f
      exact diamondWithTriangleFace0SelectedArcPureDartCycle hfmem
    · by_cases h1 : f = (1 : DiamondWithTriangleFace)
      · subst f
        exact diamondWithTriangleFace1SelectedArcPureDartCycle hfmem
      · have h2 : f = (2 : DiamondWithTriangleFace) := by
          rcases f with ⟨n, hn⟩
          have hn012 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
          rcases hn012 with rfl | rfl | rfl
          · exact False.elim (h0 rfl)
          · exact False.elim (h1 rfl)
          · rfl
        subst f
        exact diamondWithTriangleFace2PureDartCycle hfmem

def diamondWithTriangleClosedWalkEmbeddingData :
    PlanarBoundaryClosedWalkEmbeddingData diamondWithTriangleEmbedding :=
  diamondWithTrianglePureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

theorem diamondWithTriangleClosedWalkEmbeddingData_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
      (diamondWithTriangleClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f := by
  intro f
  let f0 : AmbientFace diamondWithTriangleEmbedding.faces :=
    ⟨(0 : DiamondWithTriangleFace), by
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaces]⟩
  let f1 : AmbientFace diamondWithTriangleEmbedding.faces :=
    ⟨(1 : DiamondWithTriangleFace), by
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaces]⟩
  let f2 : AmbientFace diamondWithTriangleEmbedding.faces :=
    ⟨(2 : DiamondWithTriangleFace), by
      simp [diamondWithTriangleEmbedding, diamondWithTriangleFaces]⟩
  have hf_cases : f = f0 ∨ f = f1 ∨ f = f2 := by
    rcases f with ⟨⟨n, hn⟩, hfmem⟩
    have hn012 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn012 with rfl | rfl | rfl
    · left
      exact Subtype.ext rfl
    · right
      left
      exact Subtype.ext rfl
    · right
      right
      exact Subtype.ext rfl
  rcases hf_cases with rfl | rfl | rfl
  · change
      (diamondWithTriangleClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f0
    refine ⟨[dt02, dt01], ?_, ?_⟩
    · decide
    · intro e
      rcases diamondWithTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · change
      (diamondWithTriangleClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f1
    refine ⟨[dt23, dt13], ?_, ?_⟩
    · decide
    · intro e
      rcases diamondWithTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · change
      (diamondWithTriangleClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f2
    refine ⟨[dt45, dt56, dt64], ?_, ?_⟩
    · decide
    · intro e
      rcases diamondWithTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide

/-- The honest facial closed-walk witness on the diamond-with-triangle embedding already upgrades
to the stronger cyclic ordered face-arc source shell. This blocks the natural workaround where the
source side is strengthened from explicit closed walks to cyclic per-face boundary order plus
selected-boundary contiguity. -/
noncomputable def diamondWithTriangleCyclicOrderedFaceArcEmbeddingData :
    PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding :=
  diamondWithTriangleClosedWalkEmbeddingData.toPlanarBoundaryCyclicOrderedFaceArcEmbeddingData
    diamondWithTriangleClosedWalkEmbeddingData_selectedBoundaryArcOnFace

theorem nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle :
    Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) :=
  ⟨diamondWithTriangleCyclicOrderedFaceArcEmbeddingData⟩

noncomputable def diamondWithTriangleSelectedBoundaryArcGeometry :
    PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding :=
  diamondWithTriangleCyclicOrderedFaceArcEmbeddingData.toPlanarBoundarySelectedBoundaryArcGeometry

theorem nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle :
    Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) :=
  ⟨diamondWithTriangleSelectedBoundaryArcGeometry⟩

def diamondWithTriangleOuterRoot : PlanarBoundaryEdgeVertex diamondWithTriangleEmbedding :=
  ⟨dt01, dt01_mem_selectedBoundarySupport⟩

def diamondWithTriangleInnerRoot : PlanarBoundaryEdgeVertex diamondWithTriangleEmbedding :=
  ⟨dt45, dt45_mem_selectedBoundarySupport⟩

def diamondWithTriangleBoundaryLabel
    (e : PlanarBoundaryEdgeVertex diamondWithTriangleEmbedding) : Bool :=
  if e.1 = dt45 ∨ e.1 = dt56 ∨ e.1 = dt64 then true else false

theorem diamondWithTriangle_boundaryEdge_eq
    (e : PlanarBoundaryEdgeVertex diamondWithTriangleEmbedding) :
    e = ⟨dt01, dt01_mem_selectedBoundarySupport⟩ ∨
      e = ⟨dt02, dt02_mem_selectedBoundarySupport⟩ ∨
      e = ⟨dt13, dt13_mem_selectedBoundarySupport⟩ ∨
      e = ⟨dt23, dt23_mem_selectedBoundarySupport⟩ ∨
      e = ⟨dt45, dt45_mem_selectedBoundarySupport⟩ ∨
      e = ⟨dt56, dt56_mem_selectedBoundarySupport⟩ ∨
      e = ⟨dt64, dt64_mem_selectedBoundarySupport⟩ := by
  rcases diamondWithTriangle_edge_eq e.1 with
    h01 | h12 | h02 | h13 | h23 | h45 | h56 | h64
  · exact Or.inl (Subtype.ext h01)
  · exact False.elim (dt12_not_mem_selectedBoundarySupport (by simpa [h12] using e.2))
  · exact Or.inr (Or.inl (Subtype.ext h02))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h13)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h23))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h45)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h56))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h64))))))

theorem diamondWithTriangleBoundaryAdj_preserves_label :
    ∀ ⦃e f : PlanarBoundaryEdgeVertex diamondWithTriangleEmbedding⦄,
      (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj e f →
        diamondWithTriangleBoundaryLabel e = diamondWithTriangleBoundaryLabel f := by
  intro e f hadj
  rcases diamondWithTriangle_boundaryEdge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases diamondWithTriangle_boundaryEdge_eq f with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact False.elim
          (by
            rcases hadj with ⟨_, v, hvE, hvF⟩
            fin_cases v <;>
              simp [dt01, dt02, dt13, dt23, dt45, dt56, dt64] at hvE hvF)

theorem diamondWithTriangleOuterRoot_ne_innerRoot :
    diamondWithTriangleOuterRoot ≠ diamondWithTriangleInnerRoot := by
  intro h
  have := congrArg Subtype.val h
  simp [diamondWithTriangleOuterRoot, diamondWithTriangleInnerRoot, dt01, dt45] at this

def diamondWithTriangleAnnulusBoundaryReachabilityData :
    PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding where
  outerRoot := diamondWithTriangleOuterRoot
  innerRoot := diamondWithTriangleInnerRoot
  hroots_ne := diamondWithTriangleOuterRoot_ne_innerRoot
  hcoverRoots := by
    intro e
    rcases diamondWithTriangle_boundaryEdge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨diamondWithTriangleOuterRoot, by simp [diamondWithTriangleOuterRoot_ne_innerRoot],
        SimpleGraph.Reachable.refl _⟩
    · refine ⟨diamondWithTriangleOuterRoot, by simp [diamondWithTriangleOuterRoot_ne_innerRoot],
        ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
            ⟨dt02, dt02_mem_selectedBoundarySupport⟩
            diamondWithTriangleOuterRoot := by
        refine ⟨?_, 0, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [diamondWithTriangleOuterRoot, dt02, dt01] at this
        · simp [dt02]
        · simp [diamondWithTriangleOuterRoot, dt01]
      exact hadj.reachable
    · refine ⟨diamondWithTriangleOuterRoot, by simp [diamondWithTriangleOuterRoot_ne_innerRoot],
        ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
            ⟨dt13, dt13_mem_selectedBoundarySupport⟩
            diamondWithTriangleOuterRoot := by
        refine ⟨?_, 1, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [diamondWithTriangleOuterRoot, dt13, dt01] at this
        · simp [dt13]
        · simp [diamondWithTriangleOuterRoot, dt01]
      exact hadj.reachable
    · refine ⟨diamondWithTriangleOuterRoot, by simp [diamondWithTriangleOuterRoot_ne_innerRoot],
        ?_⟩
      have h23_13 :
          (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Reachable
            ⟨dt23, dt23_mem_selectedBoundarySupport⟩
            ⟨dt13, dt13_mem_selectedBoundarySupport⟩ := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
              ⟨dt23, dt23_mem_selectedBoundarySupport⟩
              ⟨dt13, dt13_mem_selectedBoundarySupport⟩ := by
          refine ⟨?_, 3, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [dt23, dt13] at this
          · simp [dt23]
          · simp [dt13]
        exact hadj.reachable
      have h13_outer :
          (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Reachable
            ⟨dt13, dt13_mem_selectedBoundarySupport⟩
            diamondWithTriangleOuterRoot := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
              ⟨dt13, dt13_mem_selectedBoundarySupport⟩
              diamondWithTriangleOuterRoot := by
          refine ⟨?_, 1, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [diamondWithTriangleOuterRoot, dt13, dt01] at this
          · simp [dt13]
          · simp [diamondWithTriangleOuterRoot, dt01]
        exact hadj.reachable
      exact h23_13.trans h13_outer
    · refine ⟨diamondWithTriangleInnerRoot, by simp,
        SimpleGraph.Reachable.refl _⟩
    · refine ⟨diamondWithTriangleInnerRoot, by simp,
        ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
            ⟨dt56, dt56_mem_selectedBoundarySupport⟩
            diamondWithTriangleInnerRoot := by
        refine ⟨?_, 5, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [diamondWithTriangleInnerRoot, dt56, dt45] at this
        · simp [dt56]
        · simp [diamondWithTriangleInnerRoot, dt45]
      exact hadj.reachable
    · refine ⟨diamondWithTriangleInnerRoot, by simp,
        ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding).Adj
            ⟨dt64, dt64_mem_selectedBoundarySupport⟩
            diamondWithTriangleInnerRoot := by
        refine ⟨?_, 4, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [diamondWithTriangleInnerRoot, dt64, dt45] at this
        · simp [dt64]
        · simp [diamondWithTriangleInnerRoot, dt45]
      exact hadj.reachable
  hsepRoots := by
    intro r s hr hs hreach
    have hlabelEq :
        diamondWithTriangleBoundaryLabel r = diamondWithTriangleBoundaryLabel s :=
      eq_of_reachable_of_eq_on_adj
        (planarBoundarySupportEndpointAdjGraph diamondWithTriangleEmbedding)
        diamondWithTriangleBoundaryLabel
        (by
          intro u v huv
          exact diamondWithTriangleBoundaryAdj_preserves_label huv)
        hreach
    have hOuterLabel :
        diamondWithTriangleBoundaryLabel diamondWithTriangleOuterRoot = false := by
      decide
    have hInnerLabel :
        diamondWithTriangleBoundaryLabel diamondWithTriangleInnerRoot = true := by
      decide
    have hr_cases : r = diamondWithTriangleOuterRoot ∨
        r = diamondWithTriangleInnerRoot := by
      simpa [diamondWithTriangleOuterRoot_ne_innerRoot] using hr
    have hs_cases : s = diamondWithTriangleOuterRoot ∨
        s = diamondWithTriangleInnerRoot := by
      simpa [diamondWithTriangleOuterRoot_ne_innerRoot] using hs
    rcases hr_cases with rfl | rfl <;> rcases hs_cases with rfl | rfl
    · rfl
    · rw [hOuterLabel, hInnerLabel] at hlabelEq
      cases hlabelEq
    · rw [hInnerLabel, hOuterLabel] at hlabelEq
      cases hlabelEq
    · rfl

def diamondWithTriangleClosedWalkAnnulusBoundarySource :
    PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields
    diamondWithTriangleAnnulusBoundaryReachabilityData
    diamondWithTriangleClosedWalkEmbeddingData
    diamondWithTriangleClosedWalkEmbeddingData_selectedBoundaryArcOnFace

theorem nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) :=
  ⟨diamondWithTriangleClosedWalkAnnulusBoundarySource⟩

/-- The full closed-walk annulus boundary-source package still does not imply the raw
endpoint-support separation.  This model has two separated boundary components and honest facial
closed walks with selected-boundary arcs, but the diamond component contains an interior edge
touching a selected-boundary edge at a primal endpoint. -/
theorem closedWalkAnnulusBoundarySource_does_not_imply_endpointSupport_disjoint_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport diamondWithTriangleEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces)) :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
    not_endpointSupport_disjoint_diamondWithTriangle⟩

/-- The preceding boundary-source countermodel is deliberately not a countermodel to the peeled
interior-dual annulus route.  In this embedding, covering the unique interior edge `dt12` would
force a peeled witness face to be one of the two diamond triangles, but both such faces contain
selected-boundary edges.  This contradicts the edge-disjoint `hpeelInterior` field of
`InteriorDualBoundaryRootAdjDistancePeelData`. -/
theorem false_of_interiorDualBoundaryRootAdjDistancePeelData_of_forcing_interiorEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    {e : G.edgeSet}
    (heInterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hforcing : ∀ {f : AmbientFace emb.faces},
      e ∈ emb.faceBoundary f.1 →
        ∃ b ∈ emb.faceBoundary f.1,
          b ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    False := by
  have hdisj : Disjoint data.peelFaces data.roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      emb.faceBoundary emb.faces data.peelFaces data.roots
      data.hpeelInterior data.hrootsBoundary
  have hcovered :
      e ∈ data.peelFaces.image
        (rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces
          data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary
            emb.faces data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge) :=
    data.hcover heInterior
  rcases Finset.mem_image.1 hcovered with ⟨f, hfPeel, hWitness⟩
  have hneq :
      f ≠ interiorDualSpanningForestRoot emb.faceBoundary
        emb.faces data.roots data.hcoverRoots data.hsepRoots f :=
    ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
      emb.faceBoundary emb.faces
      data.peelFaces data.roots data.hcoverRoots data.hsepRoots hdisj hfPeel
  rcases parentTowardsRoot_spec_of_ne
      (T := interiorDualSpanningForest emb.faceBoundary emb.faces)
      (root := interiorDualSpanningForestRoot emb.faceBoundary
        emb.faces data.roots data.hcoverRoots data.hsepRoots)
      (u := f)
      (h := reachable_interiorDualSpanningForestRoot
        emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots f)
      hneq with ⟨p, hfp, _hadj, _hdist⟩
  have hfWitness :
      rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces
          data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary
            emb.faces data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge f ∈ emb.faceBoundary f.1 :=
    rootedSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
      emb.faceBoundary emb.faces
      data.hunique
      (interiorDualSpanningForestRoot emb.faceBoundary
        emb.faces data.roots data.hcoverRoots data.hsepRoots)
      data.fallbackEdge hfp
  have heFace : e ∈ emb.faceBoundary f.1 := by
    simpa [hWitness] using hfWitness
  rcases hforcing heFace with ⟨b, hbf, hbBoundary⟩
  exact (Finset.disjoint_left.mp (data.hpeelInterior f hfPeel)) hbf hbBoundary

theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  rintro ⟨data⟩
  exact
    false_of_interiorDualBoundaryRootAdjDistancePeelData_of_forcing_interiorEdge
      data dt12_mem_interiorEdgeSupport
      (fun hf12 =>
        exists_selectedBoundarySupport_of_dt12_mem_faceBoundary_diamondWithTriangle hf12)

/-- The honest closed-walk annulus boundary source on the diamond-with-triangle embedding still
does not reach the peeled interior-dual route. The source-side boundary geometry exists, but the
interior-dual boundary-root adjacency-distance package is empty on this embedding. -/
theorem
    closedWalkAnnulusBoundarySource_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) :=
  ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- The diamond-with-triangle embedding is a finite countermodel to deriving the current
boundary-root interior-dual distance package from raw closed-walk annulus-boundary source data
alone. -/
theorem not_forall_closedWalkSource_implies_interiorDualRootDistance_diamondWithTriangle :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph},
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
          emb.faces emb.faceBoundary) := by
  intro h
  exact not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle
    (h nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle)

/-- Strengthening the same source embedding to the cyclic ordered face-arc shell still does not
start the current peeled interior-dual route. The diamond-with-triangle embedding carries both the
annulus boundary reachability package and the stronger cyclic per-face boundary order with
selected-boundary arcs, but the peeled interior-dual adjacency-distance package remains empty. -/
theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- Weakening the source to the bundled selected-boundary arc geometry still does not start the
peeled interior-dual route on the diamond-with-triangle embedding. So even after discarding the
cyclic face-order data and retaining only one contiguous selected-boundary arc on each chosen face
boundary run, the rooted interior-dual adjacency-distance package remains empty. -/
theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- The same diamond-with-triangle model blocks the weaker construction-side annulus route as
soon as peeled faces are required to be edge-disjoint from the selected boundary support. The
only interior edge `dt12` lies on the two diamond faces, but each such face also contains a
selected-boundary edge, so no peeled face can witness `dt12`. -/
theorem
    false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_of_forcing_interiorEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    {e : G.edgeSet}
    (heInterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hforcing : ∀ {f : AmbientFace emb.faces},
      e ∈ emb.faceBoundary f.1 →
        ∃ b ∈ emb.faceBoundary f.1,
          b ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    False := by
  have hcovered : e ∈ data.peelFaces.image data.witnessEdge := data.hcover heInterior
  rcases Finset.mem_image.1 hcovered with ⟨f, hfPeel, hWitness⟩
  have hfWitness : data.witnessEdge f ∈ emb.faceBoundary f.1 := data.hwitness f hfPeel
  have heFace : e ∈ emb.faceBoundary f.1 := by
    simpa [hWitness] using hfWitness
  rcases hforcing heFace with ⟨b, hbf, hbBoundary⟩
  exact (Finset.disjoint_left.mp (hpeelInterior f hfPeel)) hbf hbBoundary

/-- The same diamond-with-triangle model blocks the weaker construction-side annulus route as
soon as peeled faces are required to be edge-disjoint from the selected boundary support. The
only interior edge `dt12` lies on the two diamond faces, but each such face also contains a
selected-boundary edge, so no peeled face can witness `dt12`. -/
theorem false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_diamondWithTriangle
    (data : PlanarBoundaryAnnulusConstruction diamondWithTriangleEmbedding)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (diamondWithTriangleEmbedding.faceBoundary f.1)
        (selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces)) :
    False := by
  exact
    false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_of_forcing_interiorEdge
      data hpeelInterior dt12_mem_interiorEdgeSupport
      (fun hf12 =>
        exists_selectedBoundarySupport_of_dt12_mem_faceBoundary_diamondWithTriangle hf12)

theorem not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData diamondWithTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_diamondWithTriangle
      data.construction data.hpeelInterior

theorem not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_diamondWithTriangle :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFacePartitionData diamondWithTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_diamondWithTriangle
      data.construction data.hpeelInterior

theorem not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_diamondWithTriangle :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionPositiveFrontierData diamondWithTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_diamondWithTriangle
      data.construction data.hpeelInterior

theorem not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_diamondWithTriangle :
    ¬ Nonempty
      (PlanarBoundaryAnnulusConstructionFaceLayerData diamondWithTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_diamondWithTriangle
      data.construction data.hpeelInterior

/-- Honest same-embedding boundary reachability plus facial closed walks still do not force even
the weakest current construction-side geometric shell. The diamond-with-triangle model has the
full closed-walk annulus-boundary source, but no peeled-interior boundary-support face data can
exist on that embedding. -/
theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          diamondWithTriangleEmbedding) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle⟩

/-- The same stronger cyclic ordered face-arc source shell also still falls short of even the
weakest current peeled-interior construction target. So strengthening the source from explicit
closed walks to cyclic ordered face arcs does not bypass the forcing-edge obstruction. -/
theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          diamondWithTriangleEmbedding) := by
  exact
    ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_diamondWithTriangle,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle⟩

/-- The same weakening to bundled selected-boundary arc geometry still does not reach even the
weakest peeled-interior construction shell on the diamond-with-triangle embedding. So keeping
only the per-face selected-boundary arc witness does not bypass the forcing-edge obstruction. -/
theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry diamondWithTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData
          diamondWithTriangleEmbedding) := by
  exact
    ⟨⟨diamondWithTriangleAnnulusBoundaryReachabilityData⟩,
      nonempty_planarBoundarySelectedBoundaryArcGeometry_diamondWithTriangle,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_diamondWithTriangle⟩

/-- A minimal edge-disjoint peeled model where endpoint no-touch still fails.  The root face
contains two selected-boundary edges and the interior edge; the peeled face is a singleton face
containing only the shared interior edge. -/
def peeledEndpointTouchGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 3)} : Set (Sym2 (Fin 4)))

def pet01 : peeledEndpointTouchGraph.edgeSet := ⟨s(0, 1), by
  simp [peeledEndpointTouchGraph]⟩

def pet12 : peeledEndpointTouchGraph.edgeSet := ⟨s(1, 2), by
  simp [peeledEndpointTouchGraph]⟩

def pet23 : peeledEndpointTouchGraph.edgeSet := ⟨s(2, 3), by
  simp [peeledEndpointTouchGraph]⟩

theorem peeledEndpointTouch_edge_eq
    (e : peeledEndpointTouchGraph.edgeSet) :
    e = pet01 ∨ e = pet12 ∨ e = pet23 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 3)) ∧
        ¬ e.1.IsDiag := by
    simpa [peeledEndpointTouchGraph] using e.2
  rcases h.1 with h01 | h12 | h23
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr (Or.inl (Subtype.ext h12))
  · exact Or.inr (Or.inr (Subtype.ext h23))

noncomputable instance peeledEndpointTouchGraph_edgeSet_fintype :
    Fintype peeledEndpointTouchGraph.edgeSet :=
  ⟨{pet01, pet12, pet23}, by
    intro e
    rcases peeledEndpointTouch_edge_eq e with rfl | rfl | rfl <;> simp⟩

private theorem peeledEndpointTouch_sym2_edges_length_le_three
    {l : List (Sym2 (Fin 4))} (hnodup : l.Nodup)
    (hmem : ∀ e ∈ l, e = s(0, 1) ∨ e = s(1, 2) ∨ e = s(2, 3)) :
    l.length ≤ 3 := by
  have hcard : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnodup
  rw [← hcard]
  have hsubset : l.toFinset ⊆ ({s(0, 1), s(1, 2), s(2, 3)} : Finset (Sym2 (Fin 4))) := by
    intro e he
    rcases List.mem_toFinset.mp he with he'
    rcases hmem e he' with rfl | rfl | rfl <;> simp
  exact Finset.card_le_card hsubset

theorem peeledEndpointTouch_no_triangle {a b c : Fin 4} :
    ¬ (peeledEndpointTouchGraph.Adj a b ∧
      peeledEndpointTouchGraph.Adj b c ∧
      peeledEndpointTouchGraph.Adj c a) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [peeledEndpointTouchGraph]

theorem peeledEndpointTouch_edges_length_le_three
    {v w : Fin 4} (p : peeledEndpointTouchGraph.Walk v w) (htrail : p.IsTrail) :
    p.length ≤ 3 := by
  have hsub :
      ∀ e ∈ p.edges, e = s(0, 1) ∨ e = s(1, 2) ∨ e = s(2, 3) := by
    intro e he
    have hedge : e ∈ peeledEndpointTouchGraph.edgeSet := p.edges_subset_edgeSet he
    have h : (e = s(0, 1) ∨ e = s(1, 2) ∨ e = s(2, 3)) ∧ ¬ e.IsDiag := by
      simpa [peeledEndpointTouchGraph] using hedge
    exact h.1
  have hle_edges :
      p.edges.length ≤ 3 :=
    peeledEndpointTouch_sym2_edges_length_le_three htrail.edges_nodup hsub
  simpa [SimpleGraph.Walk.length_edges] using hle_edges

theorem peeledEndpointTouchGraph_isAcyclic : peeledEndpointTouchGraph.IsAcyclic := by
  intro v c hc
  have hle : c.length ≤ 3 := peeledEndpointTouch_edges_length_le_three c hc.isTrail
  have hge : 3 ≤ c.length := hc.three_le_length
  have hlen : c.length = 3 := by omega
  cases c with
  | nil =>
      simp at hlen
  | cons h1 c1 =>
      cases c1 with
      | nil =>
          simp at hlen
      | cons h2 c2 =>
          cases c2 with
          | nil =>
              simp at hlen
          | cons h3 c3 =>
              cases c3 with
              | nil =>
                  exact peeledEndpointTouch_no_triangle ⟨h1, h2, h3⟩
              | cons h4 c4 =>
                  simp at hlen

abbrev PeeledEndpointTouchFace := Fin 2

def peeledEndpointTouchFaces : Finset PeeledEndpointTouchFace := Finset.univ

def peeledEndpointTouchFaceBoundary :
    PeeledEndpointTouchFace → Finset peeledEndpointTouchGraph.edgeSet
  | ⟨0, _⟩ => {pet01, pet12, pet23}
  | ⟨1, _⟩ => {pet12}

theorem totalIncidenceCount_pet01 :
    totalIncidenceCount peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces pet01 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      peeledEndpointTouchFaces.filter
          (fun f => pet01 ∈ peeledEndpointTouchFaceBoundary f) =
        {(0 : PeeledEndpointTouchFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

theorem totalIncidenceCount_pet12 :
    totalIncidenceCount peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces pet12 = 2 := by
  unfold totalIncidenceCount
  have hfilter :
      peeledEndpointTouchFaces.filter
          (fun f => pet12 ∈ peeledEndpointTouchFaceBoundary f) =
        peeledEndpointTouchFaces := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp [peeledEndpointTouchFaces]

theorem totalIncidenceCount_pet23 :
    totalIncidenceCount peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces pet23 = 1 := by
  unfold totalIncidenceCount
  have hfilter :
      peeledEndpointTouchFaces.filter
          (fun f => pet23 ∈ peeledEndpointTouchFaceBoundary f) =
        {(0 : PeeledEndpointTouchFace)} := by
    ext f
    fin_cases f <;> decide
  rw [hfilter]
  simp

def peeledEndpointTouchEmbedding : PlaneEmbeddingWithBoundary peeledEndpointTouchGraph where
  Face := PeeledEndpointTouchFace
  faceDecidableEq := inferInstance
  faces := peeledEndpointTouchFaces
  faceBoundary := peeledEndpointTouchFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases peeledEndpointTouch_edge_eq e with rfl | rfl | rfl
    · rw [Finset.mem_biUnion]
      exact ⟨(0 : PeeledEndpointTouchFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(0 : PeeledEndpointTouchFace), by exact Finset.mem_univ _, by decide⟩
    · rw [Finset.mem_biUnion]
      exact ⟨(0 : PeeledEndpointTouchFace), by exact Finset.mem_univ _, by decide⟩
  edge_one_or_two_faces := by
    intro e _he
    rcases peeledEndpointTouch_edge_eq e with rfl | rfl | rfl
    · left
      exact totalIncidenceCount_pet01
    · right
      exact totalIncidenceCount_pet12
    · left
      exact totalIncidenceCount_pet23

theorem pet01_mem_selectedBoundarySupport :
    pet01 ∈ selectedBoundarySupport
      peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
      peeledEndpointTouchEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(0 : PeeledEndpointTouchFace), by
        change (0 : PeeledEndpointTouchFace) ∈ peeledEndpointTouchFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_pet01⟩

theorem pet23_mem_selectedBoundarySupport :
    pet23 ∈ selectedBoundarySupport
      peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
      peeledEndpointTouchEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(0 : PeeledEndpointTouchFace), by
        change (0 : PeeledEndpointTouchFace) ∈ peeledEndpointTouchFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_pet23⟩

theorem pet12_mem_interiorEdgeSupport :
    pet12 ∈ interiorEdgeSupport peeledEndpointTouchEmbedding.faceBoundary
      peeledEndpointTouchEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by
      rw [Finset.mem_biUnion]
      exact ⟨(0 : PeeledEndpointTouchFace), by
        change (0 : PeeledEndpointTouchFace) ∈ peeledEndpointTouchFaces
        exact Finset.mem_univ _, by decide⟩,
    totalIncidenceCount_pet12⟩

theorem pet12_not_mem_selectedBoundarySupport :
    pet12 ∉ selectedBoundarySupport
      peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
      peeledEndpointTouchEmbedding.faces := by
  intro h
  have hcount :
      totalIncidenceCount peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces pet12 = 1 :=
    (mem_selectedBoundarySupport_iff peeledEndpointTouchEmbedding.faceBoundary
      peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces).1 h |>.2
  simp [peeledEndpointTouchEmbedding, totalIncidenceCount_pet12] at hcount

theorem peeledEndpointTouch_interiorEdgeSupport_eq_singleton :
    interiorEdgeSupport peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces = {pet12} := by
  ext e
  constructor
  · intro he
    rcases peeledEndpointTouch_edge_eq e with rfl | rfl | rfl
    · have hcount :
          totalIncidenceCount peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces pet01 = 2 :=
        (mem_interiorEdgeSupport_iff peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces).1 he |>.2
      simp [peeledEndpointTouchEmbedding, totalIncidenceCount_pet01] at hcount
    · simp
    · have hcount :
          totalIncidenceCount peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces pet23 = 2 :=
        (mem_interiorEdgeSupport_iff peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces).1 he |>.2
      simp [peeledEndpointTouchEmbedding, totalIncidenceCount_pet23] at hcount
  · intro he
    have he' : e = pet12 := by
      simpa using he
    subst e
    exact pet12_mem_interiorEdgeSupport

theorem vertex_one_mem_pet01 : (1 : Fin 4) ∈ (pet01 : Sym2 (Fin 4)) := by
  simp [pet01]

theorem vertex_zero_mem_pet01 : (0 : Fin 4) ∈ (pet01 : Sym2 (Fin 4)) := by
  simp [pet01]

theorem vertex_one_mem_pet12 : (1 : Fin 4) ∈ (pet12 : Sym2 (Fin 4)) := by
  simp [pet12]

theorem vertex_two_mem_pet12 : (2 : Fin 4) ∈ (pet12 : Sym2 (Fin 4)) := by
  simp [pet12]

theorem vertex_two_mem_pet23 : (2 : Fin 4) ∈ (pet23 : Sym2 (Fin 4)) := by
  simp [pet23]

theorem vertex_three_mem_pet23 : (3 : Fin 4) ∈ (pet23 : Sym2 (Fin 4)) := by
  simp [pet23]

theorem not_endpointSupport_disjoint_peeledEndpointTouch :
    ¬ Disjoint (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding)
      (edgeEndpointSupport
        (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) := by
  intro hdisj
  have hNoEndpoint :
      ∀ v : Fin 4,
        (∃ e ∈ interiorEdgeSupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces, v ∈ (e : Sym2 (Fin 4))) →
          ∀ e ∈ selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces,
            v ∉ (e : Sym2 (Fin 4)) := by
    exact
      (edgeEndpointSupport_disjoint_iff_no_shared_endpoint
        (interiorEdgeSupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces)
        (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)).1
        (by simpa [interiorEdgeEndpointSupport] using hdisj)
  exact hNoEndpoint 1 ⟨pet12, pet12_mem_interiorEdgeSupport, vertex_one_mem_pet12⟩
    pet01 pet01_mem_selectedBoundarySupport vertex_one_mem_pet01

theorem vertex_one_mem_interiorEdgeEndpointSupport_peeledEndpointTouch :
    (1 : Fin 4) ∈ interiorEdgeEndpointSupport peeledEndpointTouchEmbedding :=
  (mem_interiorEdgeEndpointSupport_iff peeledEndpointTouchEmbedding).2
    ⟨pet12, pet12_mem_interiorEdgeSupport, vertex_one_mem_pet12⟩

theorem vertex_one_not_mem_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    (1 : Fin 4) ∉
      selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding :=
  not_mem_verticesAvoidingEdgeSupport_of_incident_boundary_edge
    pet01_mem_selectedBoundarySupport vertex_one_mem_pet01

theorem vertex_two_mem_interiorEdgeEndpointSupport_peeledEndpointTouch :
    (2 : Fin 4) ∈ interiorEdgeEndpointSupport peeledEndpointTouchEmbedding :=
  (mem_interiorEdgeEndpointSupport_iff peeledEndpointTouchEmbedding).2
    ⟨pet12, pet12_mem_interiorEdgeSupport, vertex_two_mem_pet12⟩

theorem vertex_two_not_mem_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    (2 : Fin 4) ∉
      selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding :=
  not_mem_verticesAvoidingEdgeSupport_of_incident_boundary_edge
    pet23_mem_selectedBoundarySupport vertex_two_mem_pet23

theorem selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch :
    selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ := by
  ext v
  constructor
  · intro hv
    rcases (mem_selectedBoundaryInteriorEdgeEndpointVertices_iff
        peeledEndpointTouchEmbedding).1 hv with ⟨hvInterior, hAvoids⟩
    rcases hvInterior with ⟨e, heInterior, hve⟩
    have he12 : e = pet12 := by
      have heSingleton : e ∈ ({pet12} : Finset peeledEndpointTouchGraph.edgeSet) := by
        simpa [peeledEndpointTouch_interiorEdgeSupport_eq_singleton] using heInterior
      simpa using heSingleton
    subst e
    fin_cases v
    · simp [pet12] at hve
    · exact False.elim
        (hAvoids pet01 pet01_mem_selectedBoundarySupport vertex_one_mem_pet01)
    · exact False.elim
        (hAvoids pet23 pet23_mem_selectedBoundarySupport vertex_two_mem_pet23)
    · simp [pet12] at hve
  · simp

theorem graphEdgeEndpointSupport_nonempty_peeledEndpointTouch :
    (graphEdgeEndpointSupport peeledEndpointTouchGraph).Nonempty :=
  ⟨1, mem_graphEdgeEndpointSupport_of_mem_edge vertex_one_mem_pet12⟩

/-- In the endpoint-touch model, every graph vertex is incident to some graph edge.  Thus the
previous graph-endpoint-subcarrier obstruction is already an arbitrary finite-carrier obstruction
on this vertex type. -/
theorem graphEdgeEndpointSupport_eq_univ_peeledEndpointTouch :
    graphEdgeEndpointSupport peeledEndpointTouchGraph = Finset.univ := by
  ext v
  constructor
  · intro _hv
    simp
  · intro _hv
    fin_cases v
    · exact mem_graphEdgeEndpointSupport_of_mem_edge vertex_zero_mem_pet01
    · exact mem_graphEdgeEndpointSupport_of_mem_edge vertex_one_mem_pet01
    · exact mem_graphEdgeEndpointSupport_of_mem_edge vertex_two_mem_pet23
    · exact mem_graphEdgeEndpointSupport_of_mem_edge vertex_three_mem_pet23

/-- In the endpoint-touch model, the selected-boundary endpoints cover the whole finite vertex
type.  Any selected-boundary purification over this graph therefore has no vertex left to use. -/
theorem selectedBoundaryEndpointSupport_eq_univ_peeledEndpointTouch :
    edgeEndpointSupport
        (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces) =
      Finset.univ := by
  ext v
  constructor
  · intro _hv
    simp
  · intro _hv
    rw [mem_edgeEndpointSupport_iff]
    fin_cases v
    · exact ⟨pet01, pet01_mem_selectedBoundarySupport, vertex_zero_mem_pet01⟩
    · exact ⟨pet01, pet01_mem_selectedBoundarySupport, vertex_one_mem_pet01⟩
    · exact ⟨pet23, pet23_mem_selectedBoundarySupport, vertex_two_mem_pet23⟩
    · exact ⟨pet23, pet23_mem_selectedBoundarySupport, vertex_three_mem_pet23⟩

theorem selectedBoundaryGraphInteriorVertices_eq_empty_peeledEndpointTouch :
    selectedBoundaryGraphInteriorVertices peeledEndpointTouchEmbedding = ∅ := by
  ext v
  constructor
  · intro hv
    rcases (mem_selectedBoundaryGraphInteriorVertices_iff
        peeledEndpointTouchEmbedding).1 hv with ⟨_hvGraph, hAvoids⟩
    fin_cases v
    · exact False.elim
        (hAvoids pet01 pet01_mem_selectedBoundarySupport vertex_zero_mem_pet01)
    · exact False.elim
        (hAvoids pet01 pet01_mem_selectedBoundarySupport vertex_one_mem_pet01)
    · exact False.elim
        (hAvoids pet23 pet23_mem_selectedBoundarySupport vertex_two_mem_pet23)
    · exact False.elim
        (hAvoids pet23 pet23_mem_selectedBoundarySupport vertex_three_mem_pet23)
  · simp

theorem not_selectedBoundaryGraphInteriorVertices_nonempty_peeledEndpointTouch :
    ¬ (selectedBoundaryGraphInteriorVertices peeledEndpointTouchEmbedding).Nonempty := by
  rintro ⟨v, hv⟩
  simp [selectedBoundaryGraphInteriorVertices_eq_empty_peeledEndpointTouch] at hv

/-- Any attempted finite interior-vertex carrier drawn from graph-edge endpoints becomes empty
after selected-boundary purification in the endpoint-touch model.  This blocks replacing the
interior-edge endpoint carrier by an arbitrary subcarrier of the graph endpoints. -/
theorem selectedBoundaryInteriorVertices_eq_empty_of_subset_graphEdgeEndpointSupport_peeledEndpointTouch
    (vertices : Finset (Fin 4))
    (hvertices : vertices ⊆ graphEdgeEndpointSupport peeledEndpointTouchGraph) :
    selectedBoundaryInteriorVertices peeledEndpointTouchEmbedding vertices = ∅ := by
  ext v
  constructor
  · intro hv
    rcases (mem_selectedBoundaryInteriorVertices_iff
        peeledEndpointTouchEmbedding vertices).1 hv with ⟨hvVertices, hAvoids⟩
    have hvGraph : v ∈ graphEdgeEndpointSupport peeledEndpointTouchGraph :=
      hvertices hvVertices
    have hvSelectedGraph :
        v ∈ selectedBoundaryGraphInteriorVertices peeledEndpointTouchEmbedding := by
      rw [selectedBoundaryGraphInteriorVertices]
      exact (mem_selectedBoundaryInteriorVertices_iff
        peeledEndpointTouchEmbedding (graphEdgeEndpointSupport peeledEndpointTouchGraph)).2
        ⟨hvGraph, hAvoids⟩
    simp [selectedBoundaryGraphInteriorVertices_eq_empty_peeledEndpointTouch] at hvSelectedGraph
  · simp

/-- Stronger arbitrary-carrier form: in the endpoint-touch model, no finite vertex carrier on the
existing vertex type survives selected-boundary purification.  Repairing the route by choosing a
different carrier inside this model is therefore impossible, not merely the graph-endpoint or
interior-edge-endpoint variants. -/
theorem selectedBoundaryInteriorVertices_eq_empty_peeledEndpointTouch
    (vertices : Finset (Fin 4)) :
    selectedBoundaryInteriorVertices peeledEndpointTouchEmbedding vertices = ∅ := by
  exact
    selectedBoundaryInteriorVertices_eq_empty_of_subset_graphEdgeEndpointSupport_peeledEndpointTouch
      vertices
      (by
        intro v _hv
        simp [graphEdgeEndpointSupport_eq_univ_peeledEndpointTouch])

theorem not_selectedBoundaryInteriorVertices_nonempty_peeledEndpointTouch
    (vertices : Finset (Fin 4)) :
    ¬ (selectedBoundaryInteriorVertices peeledEndpointTouchEmbedding vertices).Nonempty := by
  rintro ⟨v, hv⟩
  simp [selectedBoundaryInteriorVertices_eq_empty_peeledEndpointTouch vertices] at hv

theorem selectedBoundaryInteriorEdgeEndpointVertices_ne_interiorEdgeEndpointSupport_peeledEndpointTouch :
    selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding ≠
      interiorEdgeEndpointSupport peeledEndpointTouchEmbedding :=
  selectedBoundaryInteriorEdgeEndpointVertices_ne_interiorEdgeEndpointSupport_of_endpoint_shared
    pet12_mem_interiorEdgeSupport pet01_mem_selectedBoundarySupport
    vertex_one_mem_pet12 vertex_one_mem_pet01

theorem selectedBoundaryInteriorEdgeEndpointVertices_strictly_refines_interiorEdgeEndpointSupport_peeledEndpointTouch :
    selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding ⊆
        interiorEdgeEndpointSupport peeledEndpointTouchEmbedding ∧
      selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding ≠
        interiorEdgeEndpointSupport peeledEndpointTouchEmbedding :=
  ⟨selectedBoundaryInteriorEdgeEndpointVertices_subset_interiorEdgeEndpointSupport
      peeledEndpointTouchEmbedding,
    selectedBoundaryInteriorEdgeEndpointVertices_ne_interiorEdgeEndpointSupport_peeledEndpointTouch⟩

def peeledEndpointTouchRootFace : AmbientFace peeledEndpointTouchEmbedding.faces :=
  ⟨(0 : PeeledEndpointTouchFace), by
    simp [peeledEndpointTouchEmbedding, peeledEndpointTouchFaces]⟩

def peeledEndpointTouchPeelFace : AmbientFace peeledEndpointTouchEmbedding.faces :=
  ⟨(1 : PeeledEndpointTouchFace), by
    simp [peeledEndpointTouchEmbedding, peeledEndpointTouchFaces]⟩

def peeledEndpointTouchRoots : Finset (AmbientFace peeledEndpointTouchEmbedding.faces) :=
  {peeledEndpointTouchRootFace}

def peeledEndpointTouchPeelFaces : Finset (AmbientFace peeledEndpointTouchEmbedding.faces) :=
  {peeledEndpointTouchPeelFace}

theorem peeledEndpointTouch_ambientFace_eq
    (f : AmbientFace peeledEndpointTouchEmbedding.faces) :
    f = peeledEndpointTouchRootFace ∨ f = peeledEndpointTouchPeelFace := by
  rcases f with ⟨⟨n, hn⟩, hf⟩
  have hn01 : n = 0 ∨ n = 1 := by omega
  rcases hn01 with rfl | rfl
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr (Subtype.ext rfl)

theorem peeledEndpointTouchRootFace_ne_peelFace :
    peeledEndpointTouchRootFace ≠ peeledEndpointTouchPeelFace := by
  decide

theorem peeledEndpointTouch_interiorDual_adj_root_peel :
    (interiorDualGraph peeledEndpointTouchEmbedding.faceBoundary
      peeledEndpointTouchEmbedding.faces).Adj
      peeledEndpointTouchRootFace peeledEndpointTouchPeelFace := by
  refine (interiorDualGraph_adj_iff peeledEndpointTouchEmbedding.faceBoundary
    peeledEndpointTouchEmbedding.faces).2 ?_
  refine ⟨?_, pet12, pet12_mem_interiorEdgeSupport, ?_, ?_⟩
  · intro h
    exact peeledEndpointTouchRootFace_ne_peelFace (Subtype.ext h)
  · decide
  · decide

theorem pairwiseUniqueSharedInteriorEdges_peeledEndpointTouch :
    PairwiseUniqueSharedInteriorEdges peeledEndpointTouchEmbedding.faceBoundary
      peeledEndpointTouchEmbedding.faces := by
  change PairwiseUniqueSharedInteriorEdges peeledEndpointTouchFaceBoundary
    peeledEndpointTouchFaces
  have hInterior :
      interiorEdgeSupport peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces =
        {pet12} := by
    simpa [peeledEndpointTouchEmbedding] using
      peeledEndpointTouch_interiorEdgeSupport_eq_singleton
  intro f _hf g _hg hfg
  have hsubset :
      sharedInteriorEdges peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces f g ⊆
        {pet12} := by
    intro e he
    have heInterior :
        e ∈ interiorEdgeSupport peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces :=
      (mem_sharedInteriorEdges_iff peeledEndpointTouchFaceBoundary
        peeledEndpointTouchFaces).1 he |>.1
    simpa [hInterior] using heInterior
  calc
    (sharedInteriorEdges peeledEndpointTouchFaceBoundary peeledEndpointTouchFaces f g).card
        ≤ ({pet12} : Finset peeledEndpointTouchGraph.edgeSet).card :=
      Finset.card_le_card hsubset
    _ = 1 := by simp

theorem hall_peeledEndpointTouch
    (e : peeledEndpointTouchGraph.edgeSet) :
    totalIncidenceCount peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces e ≤ 2 := by
  rcases peeledEndpointTouch_edge_eq e with rfl | rfl | rfl
  · simp [peeledEndpointTouchEmbedding, totalIncidenceCount_pet01]
  · simp [peeledEndpointTouchEmbedding, totalIncidenceCount_pet12]
  · simp [peeledEndpointTouchEmbedding, totalIncidenceCount_pet23]

theorem rootSetCovers_peeledEndpointTouch :
    RootSetCovers
      (interiorDualGraph peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces)
      peeledEndpointTouchRoots := by
  intro f
  rcases peeledEndpointTouch_ambientFace_eq f with rfl | rfl
  · exact ⟨peeledEndpointTouchRootFace, by simp [peeledEndpointTouchRoots],
      SimpleGraph.Reachable.refl _⟩
  · exact ⟨peeledEndpointTouchRootFace, by simp [peeledEndpointTouchRoots],
      peeledEndpointTouch_interiorDual_adj_root_peel.symm.reachable⟩

theorem rootSetSeparated_peeledEndpointTouch :
    RootSetSeparated
      (interiorDualGraph peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces)
      peeledEndpointTouchRoots := by
  intro r s hr hs _hreach
  have hr' : r = peeledEndpointTouchRootFace := by
    simpa [peeledEndpointTouchRoots] using hr
  have hs' : s = peeledEndpointTouchRootFace := by
    simpa [peeledEndpointTouchRoots] using hs
  exact hr'.trans hs'.symm

def peeledEndpointTouchFallbackEdge
    (_f : AmbientFace peeledEndpointTouchEmbedding.faces) :
    peeledEndpointTouchGraph.edgeSet :=
  pet01

theorem peeledEndpointTouch_rootedWitness_peel_eq :
    rootedSharedInteriorEdgeOfPairwiseUnique
        peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
        pairwiseUniqueSharedInteriorEdges_peeledEndpointTouch
        (interiorDualSpanningForestRoot peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchRoots
          rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch)
        peeledEndpointTouchFallbackEdge peeledEndpointTouchPeelFace = pet12 := by
  let rootFace : AmbientFace peeledEndpointTouchEmbedding.faces →
      AmbientFace peeledEndpointTouchEmbedding.faces :=
    interiorDualSpanningForestRoot peeledEndpointTouchEmbedding.faceBoundary
      peeledEndpointTouchEmbedding.faces peeledEndpointTouchRoots
      rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch
  have hdisj : Disjoint peeledEndpointTouchPeelFaces peeledEndpointTouchRoots := by
    rw [Finset.disjoint_left]
    intro f hfPeel hfRoot
    have hfPeel' : f = peeledEndpointTouchPeelFace := by
      simpa [peeledEndpointTouchPeelFaces] using hfPeel
    have hfRoot' : f = peeledEndpointTouchRootFace := by
      simpa [peeledEndpointTouchRoots] using hfRoot
    exact peeledEndpointTouchRootFace_ne_peelFace (hfRoot'.symm.trans hfPeel')
  have hneq :
      peeledEndpointTouchPeelFace ≠ rootFace peeledEndpointTouchPeelFace :=
    ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
      peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
      peeledEndpointTouchPeelFaces peeledEndpointTouchRoots
      rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch
      hdisj (by simp [peeledEndpointTouchPeelFaces])
  rcases parentTowardsRoot_spec_of_ne
      (T := interiorDualSpanningForest peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces)
      (root := rootFace)
      (u := peeledEndpointTouchPeelFace)
      (h := reachable_interiorDualSpanningForestRoot
        peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
        peeledEndpointTouchRoots rootSetCovers_peeledEndpointTouch
        rootSetSeparated_peeledEndpointTouch peeledEndpointTouchPeelFace)
      hneq with ⟨p, hfp, _hadj, _hdist⟩
  have hpeel : pet12 ∈
      peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchPeelFace.1 := by
    decide
  have hp : pet12 ∈ peeledEndpointTouchEmbedding.faceBoundary p.1 := by
    rcases peeledEndpointTouch_ambientFace_eq p with rfl | rfl <;> decide
  exact rootedSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
    peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
    pairwiseUniqueSharedInteriorEdges_peeledEndpointTouch rootFace
    peeledEndpointTouchFallbackEdge hall_peeledEndpointTouch hfp hpeel hp

theorem hpeelInterior_peeledEndpointTouch :
    ∀ f ∈ peeledEndpointTouchPeelFaces,
      Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
        (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces) := by
  intro f hf
  have hf' : f = peeledEndpointTouchPeelFace := by
    simpa [peeledEndpointTouchPeelFaces] using hf
  subst f
  rw [Finset.disjoint_left]
  intro e heFace heBoundary
  have he : e = pet12 := by
    simpa [peeledEndpointTouchEmbedding, peeledEndpointTouchFaceBoundary,
      peeledEndpointTouchPeelFace] using heFace
  exact pet12_not_mem_selectedBoundarySupport (by simpa [he] using heBoundary)

theorem hcover_peeledEndpointTouch :
    interiorEdgeSupport peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces ⊆
      peeledEndpointTouchPeelFaces.image
        (rootedSharedInteriorEdgeOfPairwiseUnique
          peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
          pairwiseUniqueSharedInteriorEdges_peeledEndpointTouch
          (interiorDualSpanningForestRoot peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchRoots
            rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch)
          peeledEndpointTouchFallbackEdge) := by
  intro e he
  have he' : e = pet12 := by
    simpa [peeledEndpointTouch_interiorEdgeSupport_eq_singleton] using he
  subst e
  refine Finset.mem_image.2 ⟨peeledEndpointTouchPeelFace, by
    simp [peeledEndpointTouchPeelFaces], ?_⟩
  exact peeledEndpointTouch_rootedWitness_peel_eq

theorem hchildren_peeledEndpointTouch :
    ∀ f ∈ peeledEndpointTouchPeelFaces,
      ∀ e ∈ (peeledEndpointTouchEmbedding.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique
          peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchEmbedding.faces
          pairwiseUniqueSharedInteriorEdges_peeledEndpointTouch
          (interiorDualSpanningForestRoot peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchRoots
            rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch)
          peeledEndpointTouchFallbackEdge f),
        e ∈ selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces ∨
          ∃ g ∈ peeledEndpointTouchPeelFaces,
            (interiorDualSpanningForest peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces).Adj f g ∧
            e ∈ peeledEndpointTouchEmbedding.faceBoundary g.1 ∧
            (interiorDualSpanningForest peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces).dist f
                (interiorDualSpanningForestRoot peeledEndpointTouchEmbedding.faceBoundary
                  peeledEndpointTouchEmbedding.faces peeledEndpointTouchRoots
                  rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch f) <
              (interiorDualSpanningForest peeledEndpointTouchEmbedding.faceBoundary
                peeledEndpointTouchEmbedding.faces).dist g
                (interiorDualSpanningForestRoot peeledEndpointTouchEmbedding.faceBoundary
                  peeledEndpointTouchEmbedding.faces peeledEndpointTouchRoots
                  rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch g) := by
  intro f hf e he
  have hf' : f = peeledEndpointTouchPeelFace := by
    simpa [peeledEndpointTouchPeelFaces] using hf
  subst f
  have hwitness := peeledEndpointTouch_rootedWitness_peel_eq
  have hempty :
      e ∈
        (peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchPeelFace.1).erase
          pet12 := by
    simpa [hwitness] using he
  simp [peeledEndpointTouchEmbedding, peeledEndpointTouchFaceBoundary,
    peeledEndpointTouchPeelFace] at hempty

def peeledEndpointTouchBoundaryData :
    PlanarBoundaryAnnulusBoundaryData peeledEndpointTouchEmbedding where
  outerAmbientBoundary := {pet01}
  innerAmbientBoundary := {pet23}
  houterAmbientBoundaryNonempty := by simp
  hinnerAmbientBoundaryNonempty := by simp
  houterAmbientBoundarySubset := by
    intro e he
    have he' : e = pet01 := by
      simpa using he
    subst e
    exact pet01_mem_selectedBoundarySupport
  hinnerAmbientBoundarySubset := by
    intro e he
    have he' : e = pet23 := by
      simpa using he
    subst e
    exact pet23_mem_selectedBoundarySupport
  hambientBoundaryCover := by
    intro e he
    rcases peeledEndpointTouch_edge_eq e with rfl | rfl | rfl
    · simp
    · exact False.elim (pet12_not_mem_selectedBoundarySupport he)
    · simp
  hambientBoundaryDisjoint := by
    rw [Finset.disjoint_left]
    intro e he01 he23
    have h01 : e = pet01 := by
      simpa using he01
    have h23 : e = pet23 := by
      simpa using he23
    have hbad : pet01 = pet23 := h01.symm.trans h23
    have hval := congrArg Subtype.val hbad
    simp [pet01, pet23] at hval

noncomputable def peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData :
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelData peeledEndpointTouchEmbedding :=
  planarBoundaryOuterBoundaryRootAdjDistancePeelDataOfCoverSeparatedOuterBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover
    peeledEndpointTouchBoundaryData
    peeledEndpointTouchPeelFaces peeledEndpointTouchRoots
    pairwiseUniqueSharedInteriorEdges_peeledEndpointTouch
    peeledEndpointTouchFallbackEdge
    rootSetCovers_peeledEndpointTouch rootSetSeparated_peeledEndpointTouch
    hpeelInterior_peeledEndpointTouch
    (by
      intro r hr
      have hr' : r = peeledEndpointTouchRootFace := by
        simpa [peeledEndpointTouchRoots] using hr
      subst r
      exact ⟨pet01, by decide, by simp [peeledEndpointTouchBoundaryData]⟩)
    hcover_peeledEndpointTouch
    hchildren_peeledEndpointTouch
    hall_peeledEndpointTouch

theorem nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
      peeledEndpointTouchEmbedding) :=
  ⟨peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData⟩

/-- The endpoint-touch model already carries the generic boundary-root adjacency-distance
interior-dual package, via the interior payload of its stronger outer-boundary-rooted data. -/
theorem nonempty_interiorDualBoundaryRootAdjDistancePeelData_peeledEndpointTouch :
    Nonempty
      (PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) :=
  ⟨peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData.interiorData⟩

noncomputable def peeledEndpointTouchAnnulusConstruction :
    PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding :=
  planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData

theorem nonempty_planarBoundaryAnnulusConstruction_peeledEndpointTouch :
    Nonempty (PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding) :=
  ⟨peeledEndpointTouchAnnulusConstruction⟩

theorem peeledEndpointTouchAnnulusConstruction_peelFaces_edge_disjoint_selectedBoundarySupport :
    ∀ f ∈ peeledEndpointTouchAnnulusConstruction.peelFaces,
      Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
        (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces) := by
  intro f hf
  have hfInterior :
      f ∈ peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData.interiorData.peelFaces := by
    simpa [peeledEndpointTouchAnnulusConstruction,
      planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData,
      planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData]
      using hf
  have hfPeel : f ∈ peeledEndpointTouchPeelFaces := by
    simpa [peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData,
      planarBoundaryOuterBoundaryRootAdjDistancePeelDataOfCoverSeparatedOuterBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover,
      interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundarySubsetRootsCanonicalRootedSharedEdgeFaceMembershipCover,
      interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover]
      using hfInterior
  exact hpeelInterior_peeledEndpointTouch f hfPeel

/-- In the peeled endpoint-touch model, the exact construction-level no-touch obligation fails:
the peeled singleton face has endpoint `1` on its interior edge, and the selected-boundary edge
`pet01` has the same endpoint. -/
theorem peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch :
    ¬ (∀ f ∈
        (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
          peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData).peelFaces,
        Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
          (edgeEndpointSupport
            (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) := by
  intro hNoTouch
  have hpeel :
      peeledEndpointTouchPeelFace ∈
        (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
          peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData).peelFaces := by
    have hInterior :
        peeledEndpointTouchPeelFace ∈
          peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData.interiorData.peelFaces := by
      simp [peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData,
        planarBoundaryOuterBoundaryRootAdjDistancePeelDataOfCoverSeparatedOuterBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover,
        interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundarySubsetRootsCanonicalRootedSharedEdgeFaceMembershipCover,
        interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover,
        peeledEndpointTouchPeelFaces]
    simpa [planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData,
      planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData]
      using hInterior
  have hFaceEndpoint :
      (1 : Fin 4) ∈ edgeEndpointSupport
        (peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchPeelFace.1) :=
    (mem_edgeEndpointSupport_iff
      (peeledEndpointTouchEmbedding.faceBoundary peeledEndpointTouchPeelFace.1)).2
      ⟨pet12, by decide, vertex_one_mem_pet12⟩
  have hBoundaryEndpoint :
      (1 : Fin 4) ∈ edgeEndpointSupport
        (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
          peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces) :=
    (mem_edgeEndpointSupport_iff
      (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
        peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)).2
      ⟨pet01, pet01_mem_selectedBoundarySupport, vertex_one_mem_pet01⟩
  exact (Finset.disjoint_left.mp
    (hNoTouch peeledEndpointTouchPeelFace hpeel)) hFaceEndpoint hBoundaryEndpoint

/-- The same failure stated in the aggregate finite-support language: the union of peeled-face
boundary endpoints is not disjoint from selected-boundary endpoints. -/
theorem not_peelFacesEndpointDisjointSelectedBoundarySupport_peeledEndpointTouchAnnulusConstruction :
    ¬ peeledEndpointTouchAnnulusConstruction.peelFacesEndpointDisjointSelectedBoundarySupport := by
  intro hNoTouch
  have hPointwise :
      ∀ f ∈
        (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
          peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData).peelFaces,
        Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
          (edgeEndpointSupport
            (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) := by
    simpa [peeledEndpointTouchAnnulusConstruction] using
      (PlanarBoundaryAnnulusConstruction.peelFacesEndpointDisjointSelectedBoundarySupport_iff
        peeledEndpointTouchAnnulusConstruction).1 hNoTouch
  exact peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch
    hPointwise

/-- The outer-boundary-rooted peeled edge-disjoint package does not imply the stronger
peeled-face endpoint no-touch obligation used by the raw-carrier bridge. -/
theorem
    outerBoundaryRootAdjDistancePeelData_does_not_imply_peelFaces_endpoint_disjoint_selectedBoundarySupport_peeledEndpointTouch :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      ¬ (∀ f ∈
          (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
            peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData).peelFaces,
          Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
                peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch⟩

/-- Even at the annulus-construction layer, peeled-face edge-disjointness from the selected
boundary support does not imply peeled-face endpoint no-touch. -/
theorem
    planarBoundaryAnnulusConstruction_edge_disjoint_peelFaces_does_not_imply_endpoint_noTouch_peeledEndpointTouch :
    ∃ data : PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding,
      (∀ f ∈ data.peelFaces,
        Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) ∧
        ¬ (∀ f ∈ data.peelFaces,
          Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
                peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) := by
  exact ⟨peeledEndpointTouchAnnulusConstruction,
    peeledEndpointTouchAnnulusConstruction_peelFaces_edge_disjoint_selectedBoundarySupport,
    peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch⟩

/-- The aggregate finite-support formulation is also not derivable from peeled-face edge
disjointness at the annulus-construction surface. -/
theorem
    planarBoundaryAnnulusConstruction_edge_disjoint_peelFaces_does_not_imply_aggregate_endpoint_noTouch_peeledEndpointTouch :
    ∃ data : PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding,
      (∀ f ∈ data.peelFaces,
        Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) ∧
        ¬ data.peelFacesEndpointDisjointSelectedBoundarySupport := by
  exact ⟨peeledEndpointTouchAnnulusConstruction,
    peeledEndpointTouchAnnulusConstruction_peelFaces_edge_disjoint_selectedBoundarySupport,
    not_peelFacesEndpointDisjointSelectedBoundarySupport_peeledEndpointTouchAnnulusConstruction⟩

/-- There is no theorem, even for this fixed embedding, deriving peeled-face endpoint no-touch
from annulus-construction data plus peeled-face edge-disjointness from the selected boundary. -/
theorem
    not_forall_planarBoundaryAnnulusConstruction_edge_disjoint_implies_endpoint_noTouch_peeledEndpointTouch :
    ¬ (∀ data : PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding,
      (∀ f ∈ data.peelFaces,
        Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) →
        ∀ f ∈ data.peelFaces,
          Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
                peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) := by
  intro h
  exact peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch
    (h peeledEndpointTouchAnnulusConstruction
      peeledEndpointTouchAnnulusConstruction_peelFaces_edge_disjoint_selectedBoundarySupport)

/-- The same fixed-embedding obstruction for the aggregate peeled-face endpoint carrier. -/
theorem
    not_forall_planarBoundaryAnnulusConstruction_edge_disjoint_implies_aggregate_endpoint_noTouch_peeledEndpointTouch :
    ¬ (∀ data : PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding,
      (∀ f ∈ data.peelFaces,
        Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) →
        data.peelFacesEndpointDisjointSelectedBoundarySupport) := by
  intro h
  exact not_peelFacesEndpointDisjointSelectedBoundarySupport_peeledEndpointTouchAnnulusConstruction
    (h peeledEndpointTouchAnnulusConstruction
      peeledEndpointTouchAnnulusConstruction_peelFaces_edge_disjoint_selectedBoundarySupport)

/-- The current outer-boundary-rooted adjacency-distance peel package is still only an
edge-disjoint package. It does not imply the raw endpoint-support separation needed to use
`interiorEdgeEndpointSupport` without the separate peeled-face endpoint no-touch hypothesis. -/
theorem outerBoundaryRootAdjDistancePeelData_does_not_imply_endpointSupport_disjoint_peeledEndpointTouch :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    not_endpointSupport_disjoint_peeledEndpointTouch⟩

/-- On the endpoint-touch embedding, no theorem can derive raw endpoint-support separation from
arbitrary outer-boundary-rooted peeled route data alone. -/
theorem
    not_forall_outerBoundaryRootAdjDistancePeelData_implies_endpointSupport_disjoint_peeledEndpointTouch :
    ¬ (∀ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding,
      Disjoint (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) := by
  intro h
  exact not_endpointSupport_disjoint_peeledEndpointTouch
    (h peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData)

/-- On the endpoint-touch embedding, no theorem can derive the peeled-face endpoint no-touch
bridge premise from arbitrary outer-boundary-rooted peeled route data alone. -/
theorem
    not_forall_outerBoundaryRootAdjDistancePeelData_implies_peelFaces_endpoint_noTouch_peeledEndpointTouch :
    ¬ (∀ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding,
      ∀ f ∈
        (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
          data).peelFaces,
        Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
          (edgeEndpointSupport
            (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) := by
  intro h
  exact peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch
    (h peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData)

theorem not_nonempty_outerBoundaryRootAdjDistancePeelDataWithEndpointSeparation_peeledEndpointTouch :
    ¬ Nonempty
      (PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
        peeledEndpointTouchEmbedding) := by
  rintro ⟨data⟩
  exact not_endpointSupport_disjoint_peeledEndpointTouch data.hEndpointDisjoint

/-- The endpoint-touch embedding carries the current outer-boundary-rooted peeled route package,
but it cannot carry the stronger route package with raw endpoint separation. -/
theorem
    outerBoundaryRootAdjDistancePeelData_does_not_imply_withEndpointSeparation_peeledEndpointTouch :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
          peeledEndpointTouchEmbedding) :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    not_nonempty_outerBoundaryRootAdjDistancePeelDataWithEndpointSeparation_peeledEndpointTouch⟩

/-- Summary certificate for the endpoint-touch obstruction at the strongest current route layer.
The same fixed embedding carries the present outer-boundary-rooted peeled annulus data and its
annulus-construction edge-disjointness, but the raw endpoint carrier is not endpoint-disjoint from
the selected boundary, the per-peeled-face and aggregate no-touch repairs fail, the stronger
endpoint-separation package is unavailable, and selected-boundary purification deletes the raw
carrier completely. -/
theorem peeledEndpointTouch_rawCarrierRepairObstructionSummary :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (∃ data : PlanarBoundaryAnnulusConstruction peeledEndpointTouchEmbedding,
        (∀ f ∈ data.peelFaces,
          Disjoint (peeledEndpointTouchEmbedding.faceBoundary f.1)
            (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) ∧
          ¬ (∀ f ∈ data.peelFaces,
            Disjoint (edgeEndpointSupport (peeledEndpointTouchEmbedding.faceBoundary f.1))
              (edgeEndpointSupport
                (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
                  peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) ∧
          ¬ data.peelFacesEndpointDisjointSelectedBoundarySupport) ∧
        ¬ Disjoint (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding)
          (edgeEndpointSupport
            (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
              peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) ∧
          ¬ Nonempty
            (PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
              peeledEndpointTouchEmbedding) ∧
            selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ := by
  refine ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch, ?_, ?_, ?_, ?_⟩
  · exact ⟨peeledEndpointTouchAnnulusConstruction,
      peeledEndpointTouchAnnulusConstruction_peelFaces_edge_disjoint_selectedBoundarySupport,
      peelFaces_endpoint_disjoint_selectedBoundarySupport_fails_peeledEndpointTouch,
      not_peelFacesEndpointDisjointSelectedBoundarySupport_peeledEndpointTouchAnnulusConstruction⟩
  · exact not_endpointSupport_disjoint_peeledEndpointTouch
  · exact not_nonempty_outerBoundaryRootAdjDistancePeelDataWithEndpointSeparation_peeledEndpointTouch
  · exact selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch

/-- In the endpoint-touch obstruction model, the selected-boundary synthesis theorem still applies
to the current peeled annulus data, but it applies over the empty purified carrier.  This separates
the positive formal synthesis endpoint from any non-vacuous raw-carrier interpretation. -/
theorem peeledEndpointTouch_emptyCarrier_synthesis
    (C₀ : peeledEndpointTouchGraph.EdgeColoring Color)
    (hC₀ : IsTaitEdgeColoring peeledEndpointTouchGraph C₀) :
    Theorem49OuterBoundaryRootSynthesis
        peeledEndpointTouchEmbedding
        peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData
        C₀ ∧
      selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ :=
  ⟨theorem49OuterBoundaryRootSynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := peeledEndpointTouchGraph)
      peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData C₀ hC₀,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch⟩

/-- The same endpoint-touch model also carries the newer two-sided annulus-root package, obtained
by forgetting that all roots happen to lie on the outer boundary component. -/
noncomputable def peeledEndpointTouchAnnulusRootAdjDistancePeelData :
    PlanarBoundaryAnnulusRootAdjDistancePeelData peeledEndpointTouchEmbedding :=
  peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData
    |>.toPlanarBoundaryAnnulusRootAdjDistancePeelData

theorem nonempty_annulusRootAdjDistancePeelData_peeledEndpointTouch :
    Nonempty
      (PlanarBoundaryAnnulusRootAdjDistancePeelData peeledEndpointTouchEmbedding) :=
  ⟨peeledEndpointTouchAnnulusRootAdjDistancePeelData⟩

/-- The newer two-sided annulus-rooted peeled data still does not force the raw endpoint-support
separation needed by the annulus-root non-vacuous repair theorem. -/
theorem annulusRootAdjDistancePeelData_does_not_imply_endpointSupport_disjoint_peeledEndpointTouch :
    Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      ¬ Disjoint (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces)) :=
  ⟨nonempty_annulusRootAdjDistancePeelData_peeledEndpointTouch,
    not_endpointSupport_disjoint_peeledEndpointTouch⟩

/-- On the endpoint-touch embedding, no theorem can derive raw endpoint-support separation from
arbitrary two-sided annulus-rooted peeled route data alone. -/
theorem not_forall_annulusRootAdjDistancePeelData_implies_endpointSupport_disjoint_peeledEndpointTouch :
    ¬ (∀ _data : PlanarBoundaryAnnulusRootAdjDistancePeelData
        peeledEndpointTouchEmbedding,
      Disjoint (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
            peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces))) := by
  intro h
  exact not_endpointSupport_disjoint_peeledEndpointTouch
    (h peeledEndpointTouchAnnulusRootAdjDistancePeelData)

/-- So the newer two-sided annulus-root synthesis theorem is subject to the same vacuity issue on
the endpoint-touch model: it holds positively, but only over the empty purified carrier. -/
theorem peeledEndpointTouch_emptyCarrier_annulusSynthesis
    (C₀ : peeledEndpointTouchGraph.EdgeColoring Color)
    (hC₀ : IsTaitEdgeColoring peeledEndpointTouchGraph C₀) :
    Theorem49AnnulusRootSynthesis
        peeledEndpointTouchEmbedding
        peeledEndpointTouchAnnulusRootAdjDistancePeelData
        C₀ ∧
      selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ :=
  ⟨theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := peeledEndpointTouchGraph)
      peeledEndpointTouchAnnulusRootAdjDistancePeelData C₀ hC₀,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch⟩

/-- The raw interior-edge endpoint carrier is nonempty in the endpoint-touch model: vertex `1`
is an endpoint of the raw interior edge `pet12`. -/
theorem interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch :
    (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty :=
  ⟨1, vertex_one_mem_interiorEdgeEndpointSupport_peeledEndpointTouch⟩

/-- The purified selected-boundary interior-edge endpoint carrier is not nonempty in the
endpoint-touch model. -/
theorem not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch :
    ¬ (selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding).Nonempty := by
  rintro ⟨v, hv⟩
  simp [selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch] at hv

/-- The endpoint-touch model refutes the non-vacuous selected-boundary synthesis surface: the
raw carrier is nonempty, but the purified carrier required by the synthesis endpoint is empty. -/
theorem not_theorem49OuterBoundaryRootNonemptySynthesis_peeledEndpointTouch
    (C₀ : peeledEndpointTouchGraph.EdgeColoring Color) :
    ¬ Theorem49OuterBoundaryRootNonemptySynthesis
        peeledEndpointTouchEmbedding
        peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData
        C₀ := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch
    h.carrier_nonempty

/-- The same purified-carrier obstruction also blocks the non-vacuous two-sided annulus-root
synthesis package. -/
theorem not_theorem49AnnulusRootNonemptySynthesis_peeledEndpointTouch
    (C₀ : peeledEndpointTouchGraph.EdgeColoring Color) :
    ¬ Theorem49AnnulusRootNonemptySynthesis
        peeledEndpointTouchEmbedding
        peeledEndpointTouchAnnulusRootAdjDistancePeelData
        C₀ := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch
    h.carrier_nonempty

/-- The current outer-boundary-rooted peeled data does not force a nonempty purified endpoint
carrier, even in a model where the raw interior-edge endpoint carrier is nonempty. -/
theorem
    outerBoundaryRootAdjDistancePeelData_does_not_imply_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        ¬ (selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding).Nonempty :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch⟩

/-- The same non-vacuity failure already appears on the newer two-sided annulus-root route
surface. -/
theorem
    annulusRootAdjDistancePeelData_does_not_imply_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        ¬ (selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding).Nonempty :=
  ⟨nonempty_annulusRootAdjDistancePeelData_peeledEndpointTouch,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch⟩

/-- Fixed-embedding universal obstruction: no theorem can derive nonemptiness of the purified
interior-edge endpoint carrier from arbitrary current peeled route data on this embedding. -/
theorem
    not_forall_outerBoundaryRootAdjDistancePeelData_implies_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    ¬ (∀ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding,
      (selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding).Nonempty) := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch
    (h peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData)

/-- The same fixed-embedding universal obstruction for the newer two-sided annulus-root route
surface. -/
theorem
    not_forall_annulusRootAdjDistancePeelData_implies_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    ¬ (∀ _data : PlanarBoundaryAnnulusRootAdjDistancePeelData
        peeledEndpointTouchEmbedding,
      (selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding).Nonempty) := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch
    (h peeledEndpointTouchAnnulusRootAdjDistancePeelData)

/-- Crux certificate for the non-vacuity failure of the purified Theorem 4.9 route surface.
The fixed endpoint-touch model admits the current peeled annulus data and has a nonempty raw
interior-edge endpoint carrier.  Nevertheless the purified carrier is empty, so every attempted
non-vacuous selected-boundary synthesis package is impossible, while the ordinary purified
synthesis still holds for any Tait coloring. -/
theorem peeledEndpointTouch_nonvacuousPurifiedSynthesisCruxObstructionSummary :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ ∧
          (∀ C₀ : peeledEndpointTouchGraph.EdgeColoring Color,
            ¬ Theorem49OuterBoundaryRootNonemptySynthesis
                peeledEndpointTouchEmbedding
                peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData
                C₀) ∧
            (∀ C₀ : peeledEndpointTouchGraph.EdgeColoring Color,
              IsTaitEdgeColoring peeledEndpointTouchGraph C₀ →
                Theorem49OuterBoundaryRootSynthesis
                  peeledEndpointTouchEmbedding
                  peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData
                  C₀) :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch,
    not_theorem49OuterBoundaryRootNonemptySynthesis_peeledEndpointTouch,
    fun C₀ hC₀ =>
      theorem49OuterBoundaryRootSynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
        (G := peeledEndpointTouchGraph)
        peeledEndpointTouchOuterBoundaryRootAdjDistancePeelData C₀ hC₀⟩

/-- The same non-vacuity crux now blocks the newer two-sided annulus-root synthesis surface as
well. The route may have abandoned the all-outer-root requirement, but unless it also rules out
endpoint-touch purification collapse, the purified endpoint remains vacuous on this model. -/
theorem peeledEndpointTouch_annulusNonvacuousPurifiedSynthesisCruxObstructionSummary :
    Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ ∧
          (∀ C₀ : peeledEndpointTouchGraph.EdgeColoring Color,
            ¬ Theorem49AnnulusRootNonemptySynthesis
                peeledEndpointTouchEmbedding
                peeledEndpointTouchAnnulusRootAdjDistancePeelData
                C₀) ∧
            (∀ C₀ : peeledEndpointTouchGraph.EdgeColoring Color,
              IsTaitEdgeColoring peeledEndpointTouchGraph C₀ →
                Theorem49AnnulusRootSynthesis
                  peeledEndpointTouchEmbedding
                  peeledEndpointTouchAnnulusRootAdjDistancePeelData
                  C₀) :=
  ⟨nonempty_annulusRootAdjDistancePeelData_peeledEndpointTouch,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch,
    not_theorem49AnnulusRootNonemptySynthesis_peeledEndpointTouch,
    fun C₀ hC₀ =>
      theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
        (G := peeledEndpointTouchGraph)
        peeledEndpointTouchAnnulusRootAdjDistancePeelData C₀ hC₀⟩

/-- Broader carrier crux certificate: in the endpoint-touch model, selected-boundary
purification empties not only the face-incidence interior-edge endpoint carrier, but every finite
candidate carrier contained in the graph-edge endpoint support.  Thus the route cannot repair the
non-vacuity problem by switching to the canonical all-graph-endpoint carrier or to any of its
subcarriers. -/
theorem peeledEndpointTouch_graphEndpointSubcarrierCruxObstructionSummary :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        (graphEdgeEndpointSupport peeledEndpointTouchGraph).Nonempty ∧
          selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ ∧
            selectedBoundaryGraphInteriorVertices peeledEndpointTouchEmbedding = ∅ ∧
              ∀ vertices : Finset (Fin 4),
                vertices ⊆ graphEdgeEndpointSupport peeledEndpointTouchGraph →
                  selectedBoundaryInteriorVertices peeledEndpointTouchEmbedding vertices = ∅ :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    graphEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch,
    selectedBoundaryGraphInteriorVertices_eq_empty_peeledEndpointTouch,
    selectedBoundaryInteriorVertices_eq_empty_of_subset_graphEdgeEndpointSupport_peeledEndpointTouch⟩

/-- Strongest carrier-level crux certificate for the endpoint-touch model.  The selected-boundary
endpoint support already covers every vertex of the graph, while the graph-edge endpoint support
is also all vertices.  Hence every finite candidate carrier on this vertex type purifies to the
empty set.  A non-vacuous repair cannot be obtained by changing the finite carrier inside this
model; it must add a genuinely stronger geometric hypothesis excluding this model or change the
strategy. -/
theorem peeledEndpointTouch_arbitraryCarrierCruxObstructionSummary :
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData
        peeledEndpointTouchEmbedding) ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        graphEdgeEndpointSupport peeledEndpointTouchGraph = Finset.univ ∧
          edgeEndpointSupport
              (selectedBoundarySupport peeledEndpointTouchEmbedding.faceBoundary
                peeledEndpointTouchEmbedding.faces peeledEndpointTouchEmbedding.faces) =
            Finset.univ ∧
            ∀ vertices : Finset (Fin 4),
              selectedBoundaryInteriorVertices peeledEndpointTouchEmbedding vertices = ∅ :=
  ⟨nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    graphEdgeEndpointSupport_eq_univ_peeledEndpointTouch,
    selectedBoundaryEndpointSupport_eq_univ_peeledEndpointTouch,
    selectedBoundaryInteriorVertices_eq_empty_peeledEndpointTouch⟩

/-- The peeled endpoint-touch graph is acyclic, so no embedding of it can carry honest
facial closed-walk geometry. -/
theorem not_nonempty_planarBoundaryClosedWalkEmbeddingData_peeledEndpointTouchGraph
    {emb : PlaneEmbeddingWithBoundary peeledEndpointTouchGraph} :
    ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData emb) := by
  exact
    not_nonempty_planarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      peeledEndpointTouchGraph_isAcyclic ⟨pet01⟩

theorem not_nonempty_planarBoundaryClosedWalkEmbeddingData_peeledEndpointTouchEmbedding :
    ¬ Nonempty (PlanarBoundaryClosedWalkEmbeddingData peeledEndpointTouchEmbedding) := by
  exact not_nonempty_planarBoundaryClosedWalkEmbeddingData_peeledEndpointTouchGraph

theorem not_admitsPlanarBoundaryClosedWalkEmbeddingData_peeledEndpointTouchGraph :
    ¬ AdmitsPlanarBoundaryClosedWalkEmbeddingData peeledEndpointTouchGraph := by
  exact
    not_admitsPlanarBoundaryClosedWalkEmbeddingData_of_isAcyclic_of_nonempty_edgeSet
      peeledEndpointTouchGraph_isAcyclic ⟨pet01⟩

/-- The endpoint-touch graph cannot satisfy the honest closed-walk annulus-boundary source:
that source already contains a facial closed-walk witness. -/
theorem not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_of_isAcyclic_of_nonempty_edgeSet
      peeledEndpointTouchGraph_isAcyclic ⟨pet01⟩

theorem admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData peeledEndpointTouchGraph := by
  exact ⟨peeledEndpointTouchEmbedding,
    nonempty_interiorDualBoundaryRootAdjDistancePeelData_peeledEndpointTouch⟩

theorem admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData peeledEndpointTouchGraph := by
  exact ⟨peeledEndpointTouchEmbedding,
    nonempty_outerBoundaryRootAdjDistancePeelData_peeledEndpointTouch⟩

theorem admitsPlanarBoundaryAnnulusRootAdjDistancePeelData_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData peeledEndpointTouchGraph := by
  exact ⟨peeledEndpointTouchEmbedding,
    nonempty_annulusRootAdjDistancePeelData_peeledEndpointTouch⟩

/-- The endpoint-touch embedding already reaches the direct boundary height-ordered witness-cover
surface through the same annulus-root interior-dual data. So the endpoint-touch collapse is not
merely a well-founded-parent or certificate-endpoint artifact. -/
noncomputable def peeledEndpointTouchPlanarBoundaryHeightOrderedFacePeelWitnessData :
    PlanarBoundaryHeightOrderedFacePeelWitnessData peeledEndpointTouchEmbedding :=
  planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
    peeledEndpointTouchAnnulusRootAdjDistancePeelData.interiorData

theorem admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData peeledEndpointTouchGraph := by
  exact ⟨peeledEndpointTouchEmbedding,
    ⟨peeledEndpointTouchPlanarBoundaryHeightOrderedFacePeelWitnessData⟩⟩

/-- The purified selected-boundary carrier is still empty on the endpoint-touch height-ordered
witness-cover model, because the witness data lives on the same embedding. -/
theorem peeledEndpointTouch_heightOrderedWitnessData_emptyCarrier :
    selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ := by
  exact selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch

/-- Even the direct boundary height-ordered witness-cover surface does not force a nonempty
purified selected-boundary carrier on the endpoint-touch model. -/
theorem
    planarBoundaryHeightOrderedFacePeelWitnessData_does_not_imply_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    ∃ emb : PlaneEmbeddingWithBoundary peeledEndpointTouchGraph,
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
        (interiorEdgeEndpointSupport emb).Nonempty ∧
          ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  refine ⟨peeledEndpointTouchEmbedding,
    ⟨peeledEndpointTouchPlanarBoundaryHeightOrderedFacePeelWitnessData⟩, ?_, ?_⟩
  · exact interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch
  · exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch

/-- Crux summary on the direct boundary height-ordered witness-cover lane: the endpoint-touch
graph already admits this earlier witness-cover endpoint, the raw interior-edge endpoint carrier is
nonempty, but the purified selected-boundary carrier is empty. -/
theorem peeledEndpointTouch_heightOrderedWitnessCarrierCruxObstructionSummary :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData peeledEndpointTouchGraph ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ := by
  exact ⟨admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_peeledEndpointTouchGraph,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    peeledEndpointTouch_heightOrderedWitnessData_emptyCarrier⟩

/-- The endpoint-touch embedding already reaches the earlier well-founded witness-cover surface
through the same annulus-root interior-dual data. So the endpoint-touch collapse is not merely a
certificate-endpoint artifact. -/
noncomputable def peeledEndpointTouchPlanarBoundaryWellFoundedFacePeelWitnessData :
    PlanarBoundaryWellFoundedFacePeelWitnessData peeledEndpointTouchEmbedding :=
  planarBoundaryWellFoundedFacePeelWitnessData_of_interiorDualWellFoundedParentPeelData
    peeledEndpointTouchAnnulusRootAdjDistancePeelData.interiorData.toInteriorDualWellFoundedParentPeelData

theorem admitsPlanarBoundaryWellFoundedFacePeelWitnessData_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData peeledEndpointTouchGraph := by
  exact ⟨peeledEndpointTouchEmbedding,
    ⟨peeledEndpointTouchPlanarBoundaryWellFoundedFacePeelWitnessData⟩⟩

/-- The purified selected-boundary carrier is still empty on the endpoint-touch witness-cover
model, because the witness data lives on the same embedding. -/
theorem peeledEndpointTouch_wellFoundedWitnessData_emptyCarrier :
    selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ := by
  exact selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch

/-- Even the earlier well-founded witness-cover surface does not force a nonempty purified
selected-boundary carrier on the endpoint-touch model. -/
theorem
    planarBoundaryWellFoundedFacePeelWitnessData_does_not_imply_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    ∃ emb : PlaneEmbeddingWithBoundary peeledEndpointTouchGraph,
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
        (interiorEdgeEndpointSupport emb).Nonempty ∧
          ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  refine ⟨peeledEndpointTouchEmbedding,
    ⟨peeledEndpointTouchPlanarBoundaryWellFoundedFacePeelWitnessData⟩, ?_, ?_⟩
  · exact interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch
  · exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch

/-- Crux summary on the direct well-founded witness-cover lane: the endpoint-touch graph already
admits the witness-cover endpoint, the raw interior-edge endpoint carrier is nonempty, but the
purified selected-boundary carrier is empty. -/
theorem peeledEndpointTouch_wellFoundedWitnessCarrierCruxObstructionSummary :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData peeledEndpointTouchGraph ∧
      (interiorEdgeEndpointSupport peeledEndpointTouchEmbedding).Nonempty ∧
        selectedBoundaryInteriorEdgeEndpointVertices peeledEndpointTouchEmbedding = ∅ := by
  exact ⟨admitsPlanarBoundaryWellFoundedFacePeelWitnessData_peeledEndpointTouchGraph,
    interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch,
    peeledEndpointTouch_wellFoundedWitnessData_emptyCarrier⟩

/-- The same endpoint-touch embedding already reaches the graph-level attached-certificate
surface through its annulus-root interior-dual data. This shows the certificate endpoint itself
does not rule out the endpoint-touch collapse. -/
noncomputable def peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate :
    PlanarBoundaryAttachedRootedFacePeelCertificate peeledEndpointTouchGraph :=
  planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualBoundaryRootAdjDistancePeelData
    peeledEndpointTouchEmbedding peeledEndpointTouchAnnulusRootAdjDistancePeelData.interiorData

theorem admitsPlanarBoundaryAttachedRootedFacePeelCertificate_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate peeledEndpointTouchGraph := by
  exact ⟨peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate⟩

/-- The attached-certificate endpoint is still vacuous on the endpoint-touch model: its ambient
embedding is exactly the same one whose purified selected-boundary carrier is empty. -/
theorem peeledEndpointTouch_attachedCertificate_emptyCarrier :
    selectedBoundaryInteriorEdgeEndpointVertices
        peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate.embedding = ∅ := by
  simpa [peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate] using
    selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_peeledEndpointTouch

/-- So the graph-level attached-certificate surface also fails to force a nonempty purified
selected-boundary carrier, even when the raw interior-edge endpoint carrier is nonempty. -/
theorem
    planarBoundaryAttachedRootedFacePeelCertificate_does_not_imply_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_peeledEndpointTouch :
    ∃ data : PlanarBoundaryAttachedRootedFacePeelCertificate peeledEndpointTouchGraph,
      (interiorEdgeEndpointSupport data.embedding).Nonempty ∧
        ¬ (selectedBoundaryInteriorEdgeEndpointVertices data.embedding).Nonempty := by
  refine ⟨peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate, ?_, ?_⟩
  · simpa [peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate] using
      interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch
  · simpa [peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate] using
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_peeledEndpointTouch

/-- Crux summary on the direct attached-certificate lane: the endpoint-touch graph already admits
the graph-level certificate endpoint, the raw interior-edge endpoint carrier is nonempty, but the
certificate's own purified selected-boundary carrier is empty. -/
theorem peeledEndpointTouch_attachedCertificateCarrierCruxObstructionSummary :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate peeledEndpointTouchGraph ∧
      (interiorEdgeEndpointSupport
          peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate.embedding).Nonempty ∧
        selectedBoundaryInteriorEdgeEndpointVertices
            peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate.embedding = ∅ := by
  refine ⟨admitsPlanarBoundaryAttachedRootedFacePeelCertificate_peeledEndpointTouchGraph, ?_, ?_⟩
  · simpa [peeledEndpointTouchPlanarBoundaryAttachedRootedFacePeelCertificate] using
      interiorEdgeEndpointSupport_nonempty_peeledEndpointTouch
  · exact peeledEndpointTouch_attachedCertificate_emptyCarrier

/-- Calibration theorem for the current route layers: the endpoint-touch graph still carries the
current outer-boundary-rooted peeled annulus data, but it cannot carry the stronger honest
closed-walk annulus-boundary source. So the former does not imply the latter. -/
theorem
    admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData peeledEndpointTouchGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact ⟨admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_peeledEndpointTouchGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph⟩

/-- Calibration theorem for the current route layers: the endpoint-touch graph still carries the
current outer-boundary-rooted peeled annulus data, but it cannot carry the stronger honest
closed-walk annulus-boundary source. So the former does not imply the latter. -/
theorem
    admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData peeledEndpointTouchGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact ⟨admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_peeledEndpointTouchGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph⟩

/-- The same calibration for the newer two-sided annulus-root route surface. The endpoint-touch
graph already carries annulus-root adjacency-distance data, but still cannot carry the honest
closed-walk annulus source because the graph is acyclic. -/
theorem
    admitsPlanarBoundaryAnnulusRootAdjDistancePeelData_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData peeledEndpointTouchGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact ⟨admitsPlanarBoundaryAnnulusRootAdjDistancePeelData_peeledEndpointTouchGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph⟩

/-- The same calibration on the direct boundary height-ordered witness-cover surface. The
endpoint-touch graph already reaches this earlier planarity-side witness endpoint, but still cannot
carry the honest closed-walk annulus source because the graph is acyclic. -/
theorem
    admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData peeledEndpointTouchGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact ⟨admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_peeledEndpointTouchGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph⟩

/-- The same calibration on the earlier well-founded witness-cover surface. The endpoint-touch
graph already reaches this planarity-side witness endpoint, but still cannot carry the honest
closed-walk annulus source because the graph is acyclic. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData peeledEndpointTouchGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact ⟨admitsPlanarBoundaryWellFoundedFacePeelWitnessData_peeledEndpointTouchGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph⟩

/-- The same calibration on the direct graph-level attached-certificate surface. The endpoint-
touch graph already reaches the certificate endpoint, but still cannot carry the honest closed-
walk annulus source because the graph is acyclic. -/
theorem
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_withoutClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate peeledEndpointTouchGraph ∧
      ¬ AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource peeledEndpointTouchGraph := by
  exact ⟨admitsPlanarBoundaryAttachedRootedFacePeelCertificate_peeledEndpointTouchGraph,
    not_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource_peeledEndpointTouchGraph⟩

end Theorem49InteriorVerticesEndpointObstruction

end Mettapedia.GraphTheory.FourColor
