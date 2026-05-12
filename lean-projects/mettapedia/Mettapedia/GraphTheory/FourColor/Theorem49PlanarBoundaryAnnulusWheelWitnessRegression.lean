import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometry
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceReplacement
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

/-- A finite annulus benchmark with a three-spoke wheel component and a disjoint inner triangle.
The wheel component has three interior spokes incident to the central vertex `0`; the selected
outer boundary is the rim triangle, so the central vertex survives selected-boundary purification.
-/
def wheelWithInnerTriangleGraph : SimpleGraph (Fin 7) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(0, 2), s(0, 3), s(1, 2), s(2, 3), s(3, 1),
        s(4, 5), s(5, 6), s(6, 4)} : Set (Sym2 (Fin 7)))

def wit01 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(0, 1), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit02 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(0, 2), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit03 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(0, 3), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit12 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(1, 2), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit23 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(2, 3), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit31 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(3, 1), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit45 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(4, 5), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit56 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(5, 6), by
  simp [wheelWithInnerTriangleGraph]⟩

def wit64 : wheelWithInnerTriangleGraph.edgeSet := ⟨s(6, 4), by
  simp [wheelWithInnerTriangleGraph]⟩

theorem wheelWithInnerTriangle_edge_eq
    (e : wheelWithInnerTriangleGraph.edgeSet) :
    e = wit01 ∨ e = wit02 ∨ e = wit03 ∨ e = wit12 ∨ e = wit23 ∨
      e = wit31 ∨ e = wit45 ∨ e = wit56 ∨ e = wit64 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(0, 2) ∨ e.1 = s(0, 3) ∨
          e.1 = s(1, 2) ∨ e.1 = s(2, 3) ∨ e.1 = s(3, 1) ∨
          e.1 = s(4, 5) ∨ e.1 = s(5, 6) ∨ e.1 = s(6, 4)) ∧
        ¬ e.1.IsDiag := by
    simpa [wheelWithInnerTriangleGraph] using e.2
  rcases h.1 with h01 | h02 | h03 | h12 | h23 | h31 | h45 | h56 | h64
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr <| Or.inl (Subtype.ext h02)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h03)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h12)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h23)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h31)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext h56)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr (Subtype.ext h64)

noncomputable instance wheelWithInnerTriangleGraph_edgeSet_fintype :
    Fintype wheelWithInnerTriangleGraph.edgeSet :=
  ⟨{wit01, wit02, wit03, wit12, wit23, wit31, wit45, wit56, wit64}, by
    intro e
    rcases wheelWithInnerTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp⟩

abbrev WheelWithInnerTriangleFace := Fin 4

def wheelWithInnerTriangleFaces : Finset WheelWithInnerTriangleFace := Finset.univ

def wheelWithInnerTriangleFaceBoundary :
    WheelWithInnerTriangleFace → Finset wheelWithInnerTriangleGraph.edgeSet
  | ⟨0, _⟩ => {wit01, wit02, wit12}
  | ⟨1, _⟩ => {wit02, wit03, wit23}
  | ⟨2, _⟩ => {wit03, wit01, wit31}
  | ⟨3, _⟩ => {wit45, wit56, wit64}

theorem totalIncidenceCount_wit01 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit01 = 2 := by
  decide

theorem totalIncidenceCount_wit02 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit02 = 2 := by
  decide

theorem totalIncidenceCount_wit03 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit03 = 2 := by
  decide

theorem totalIncidenceCount_wit12 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit12 = 1 := by
  decide

theorem totalIncidenceCount_wit23 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit23 = 1 := by
  decide

theorem totalIncidenceCount_wit31 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit31 = 1 := by
  decide

theorem totalIncidenceCount_wit45 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit45 = 1 := by
  decide

theorem totalIncidenceCount_wit56 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit56 = 1 := by
  decide

theorem totalIncidenceCount_wit64 :
    totalIncidenceCount wheelWithInnerTriangleFaceBoundary
      wheelWithInnerTriangleFaces wit64 = 1 := by
  decide

def wheelWithInnerTriangleEmbedding :
    PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph where
  Face := WheelWithInnerTriangleFace
  faceDecidableEq := inferInstance
  faces := wheelWithInnerTriangleFaces
  faceBoundary := wheelWithInnerTriangleFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases wheelWithInnerTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases wheelWithInnerTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

def wheelFace0 : AmbientFace wheelWithInnerTriangleEmbedding.faces :=
  ⟨(0 : WheelWithInnerTriangleFace), by
    simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaces]⟩

def wheelFace1 : AmbientFace wheelWithInnerTriangleEmbedding.faces :=
  ⟨(1 : WheelWithInnerTriangleFace), by
    simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaces]⟩

def wheelFace2 : AmbientFace wheelWithInnerTriangleEmbedding.faces :=
  ⟨(2 : WheelWithInnerTriangleFace), by
    simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaces]⟩

theorem wit01_ne_wit02 : wit01 ≠ wit02 := by
  decide

theorem wit01_ne_wit03 : wit01 ≠ wit03 := by
  decide

theorem wit02_ne_wit03 : wit02 ≠ wit03 := by
  decide

theorem wit01_mem_faceBoundary_iff
    (f : AmbientFace wheelWithInnerTriangleEmbedding.faces) :
    wit01 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 ↔
      f = wheelFace0 ∨ f = wheelFace2 := by
  rcases f with ⟨⟨n, hn⟩, hf⟩
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn_cases with rfl | rfl | rfl | rfl <;>
    simp [wheelFace0, wheelFace2, wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleFaceBoundary] <;>
    decide

theorem wit02_mem_faceBoundary_iff
    (f : AmbientFace wheelWithInnerTriangleEmbedding.faces) :
    wit02 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 ↔
      f = wheelFace0 ∨ f = wheelFace1 := by
  rcases f with ⟨⟨n, hn⟩, hf⟩
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn_cases with rfl | rfl | rfl | rfl <;>
    simp [wheelFace0, wheelFace1, wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleFaceBoundary] <;>
    decide

theorem wit03_mem_faceBoundary_iff
    (f : AmbientFace wheelWithInnerTriangleEmbedding.faces) :
    wit03 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 ↔
      f = wheelFace1 ∨ f = wheelFace2 := by
  rcases f with ⟨⟨n, hn⟩, hf⟩
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn_cases with rfl | rfl | rfl | rfl <;>
    simp [wheelFace1, wheelFace2, wheelWithInnerTriangleEmbedding,
      wheelWithInnerTriangleFaceBoundary] <;>
    decide

theorem wit01_mem_interiorEdgeSupport :
    wit01 ∈ interiorEdgeSupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit01⟩

theorem wit02_mem_interiorEdgeSupport :
    wit02 ∈ interiorEdgeSupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit02⟩

theorem wit03_mem_interiorEdgeSupport :
    wit03 ∈ interiorEdgeSupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit03⟩

theorem exists_two_distinct_interior_edges_on_wheelFace0_boundary :
    ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary (0 : WheelWithInnerTriangleFace),
      ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary (0 : WheelWithInnerTriangleFace),
        e₁ ≠ e₂ ∧
          e₁ ∈ interiorEdgeSupport
            wheelWithInnerTriangleEmbedding.faceBoundary
            wheelWithInnerTriangleEmbedding.faces ∧
          e₂ ∈ interiorEdgeSupport
            wheelWithInnerTriangleEmbedding.faceBoundary
            wheelWithInnerTriangleEmbedding.faces := by
  exact
    ⟨wit01, by decide, wit02, by decide, by decide,
      wit01_mem_interiorEdgeSupport, wit02_mem_interiorEdgeSupport⟩

theorem exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary :
    ∃ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
      ∃ e₁ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
        ∃ e₂ ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1,
          e₁ ≠ e₂ ∧
            e₁ ∈ interiorEdgeSupport
              wheelWithInnerTriangleEmbedding.faceBoundary
              wheelWithInnerTriangleEmbedding.faces ∧
            e₂ ∈ interiorEdgeSupport
              wheelWithInnerTriangleEmbedding.faceBoundary
              wheelWithInnerTriangleEmbedding.faces := by
  exact
    ⟨⟨(0 : WheelWithInnerTriangleFace),
        by simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaces]⟩,
      exists_two_distinct_interior_edges_on_wheelFace0_boundary⟩

theorem not_nonempty_planarBoundaryCanonicalWitnessChoice_wheelWithInnerTriangle
    (boundaryData : PlanarBoundaryAnnulusBoundaryData wheelWithInnerTriangleEmbedding) :
    ¬ Nonempty (PlanarBoundaryCanonicalWitnessChoice boundaryData) := by
  exact
    not_nonempty_planarBoundaryCanonicalWitnessChoice_of_exists_two_distinct_interior_edges_on_faceBoundary
      boundaryData exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary

theorem not_exists_oneCollar_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle :
    ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 := by
  exact
    not_exists_planarBoundaryAnnulusCollarGeometry_of_numCollars_eq_one_and_exists_two_distinct_interior_edges_on_faceBoundary
      exists_two_distinct_interior_edges_on_wheelWithInnerTriangle_boundary

/-- The concrete wheel obstruction is visible directly at the local at-most-one-interior-edge
premise: face `0` filters to the two interior spokes `wit01` and `wit02`. -/
theorem wheelWithInnerTriangle_face0_interiorEdgeFilter_card :
    ((wheelWithInnerTriangleEmbedding.faceBoundary (0 : WheelWithInnerTriangleFace)).filter
        (· ∈ interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces)).card = 2 := by
  decide

/-- The wheel embedding cannot satisfy the local at-most-one-interior-edge premise used by the
generic canonical-witness constructor. -/
theorem not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace :
    ¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
      ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
            wheelWithInnerTriangleEmbedding.faces)).card ≤ 1 := by
  intro hAtMost
  have h0 := hAtMost
    ⟨(0 : WheelWithInnerTriangleFace),
      by simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaces]⟩
  rw [wheelWithInnerTriangle_face0_interiorEdgeFilter_card] at h0
  omega

/-- No honest closed-walk source on this fixed wheel embedding can supply the local
at-most-one-interior-edge package used by the sufficient condition: the failure is already the
face-local two-spoke obstruction, independent of the fallback and boundary-rest fields. -/
theorem
    not_exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_wheelWithInnerTriangleEmbedding :
    ¬ ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding,
      ∃ fallbackEdge : AmbientFace wheelWithInnerTriangleEmbedding.faces →
          wheelWithInnerTriangleGraph.edgeSet,
        (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
          fallbackEdge f ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1) ∧
          (∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
            ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces)).card ≤
              (1 : ℕ)) ∧
            ∀ (f : AmbientFace wheelWithInnerTriangleEmbedding.faces)
                {e : wheelWithInnerTriangleGraph.edgeSet},
              e ∈ wheelWithInnerTriangleEmbedding.faceBoundary f.1 →
                e ∉ interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
                  wheelWithInnerTriangleEmbedding.faces →
                e ∈
                  source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                    source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  rintro ⟨_source, _fallbackEdge, _hfallback, hAtMost, _hboundaryRest⟩
  exact not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace hAtMost

theorem wit01_not_mem_selectedBoundarySupport :
    wit01 ∉ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  rintro ⟨_, hcount⟩
  have hcount' :
      totalIncidenceCount wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wit01 = 2 := by
    simpa [wheelWithInnerTriangleEmbedding] using totalIncidenceCount_wit01
  rw [hcount'] at hcount
  omega

theorem wit02_not_mem_selectedBoundarySupport :
    wit02 ∉ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  rintro ⟨_, hcount⟩
  have hcount' :
      totalIncidenceCount wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wit02 = 2 := by
    simpa [wheelWithInnerTriangleEmbedding] using totalIncidenceCount_wit02
  rw [hcount'] at hcount
  omega

theorem wit03_not_mem_selectedBoundarySupport :
    wit03 ∉ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  rintro ⟨_, hcount⟩
  have hcount' :
      totalIncidenceCount wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wit03 = 2 := by
    simpa [wheelWithInnerTriangleEmbedding] using totalIncidenceCount_wit03
  rw [hcount'] at hcount
  omega

/-- The wheel benchmark also blocks the replacement witness-cover surface itself.  Covering one
interior spoke forces a peeled face to witness it; the other interior spoke on that triangular
wheel face must then be witnessed at a strictly later height.  Walking around the three wheel
faces returns to a later witness for the first spoke on the original face, contradicting
irreflexivity of `<` on heights. -/
theorem not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle :
    ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) := by
  rintro ⟨data⟩
  rcases Finset.mem_image.1 (data.hcover wit01_mem_interiorEdgeSupport) with
    ⟨f01, hf01Peel, hf01Witness⟩
  have hf01WitnessMem :
      data.witnessEdge f01 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f01.1 :=
    data.hwitness f01 hf01Peel
  have hwit01_f01 :
      wit01 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f01.1 := by
    simpa [hf01Witness] using hf01WitnessMem
  rcases (wit01_mem_faceBoundary_iff f01).1 hwit01_f01 with hf01_eq_f0 | hf01_eq_f2
  · have hwit02_f01 :
        wit02 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f01.1 := by
      rw [hf01_eq_f0]
      decide
    have hwit02_erase :
        wit02 ∈
          (wheelWithInnerTriangleEmbedding.faceBoundary f01.1).erase
            (data.witnessEdge f01) := by
      refine Finset.mem_erase.2 ⟨?_, hwit02_f01⟩
      intro h
      exact wit01_ne_wit02 (hf01Witness.symm.trans h.symm)
    rcases data.hrest f01 hf01Peel wit02 hwit02_erase with
      hwit02Boundary | ⟨f02, hf02Peel, hf02Witness, hlt01_02⟩
    · exact wit02_not_mem_selectedBoundarySupport hwit02Boundary
    have hf02WitnessMem :
        data.witnessEdge f02 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f02.1 :=
      data.hwitness f02 hf02Peel
    have hwit02_f02 :
        wit02 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f02.1 := by
      simpa [hf02Witness] using hf02WitnessMem
    have hf02_ne_f01 : f02 ≠ f01 := by
      intro h
      subst h
      exact wit01_ne_wit02 (hf01Witness.symm.trans hf02Witness)
    have hf02_eq_f1 : f02 = wheelFace1 := by
      rcases (wit02_mem_faceBoundary_iff f02).1 hwit02_f02 with hf02_eq_f0 | hf02_eq_f1
      · exact False.elim (hf02_ne_f01 (hf02_eq_f0.trans hf01_eq_f0.symm))
      · exact hf02_eq_f1
    have hwit03_f02 :
        wit03 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f02.1 := by
      rw [hf02_eq_f1]
      decide
    have hwit03_erase :
        wit03 ∈
          (wheelWithInnerTriangleEmbedding.faceBoundary f02.1).erase
            (data.witnessEdge f02) := by
      refine Finset.mem_erase.2 ⟨?_, hwit03_f02⟩
      intro h
      exact wit02_ne_wit03 (hf02Witness.symm.trans h.symm)
    rcases data.hrest f02 hf02Peel wit03 hwit03_erase with
      hwit03Boundary | ⟨f03, hf03Peel, hf03Witness, hlt02_03⟩
    · exact wit03_not_mem_selectedBoundarySupport hwit03Boundary
    have hf03WitnessMem :
        data.witnessEdge f03 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f03.1 :=
      data.hwitness f03 hf03Peel
    have hwit03_f03 :
        wit03 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f03.1 := by
      simpa [hf03Witness] using hf03WitnessMem
    have hf03_ne_f02 : f03 ≠ f02 := by
      intro h
      subst h
      exact wit02_ne_wit03 (hf02Witness.symm.trans hf03Witness)
    have hf03_eq_f2 : f03 = wheelFace2 := by
      rcases (wit03_mem_faceBoundary_iff f03).1 hwit03_f03 with hf03_eq_f1 | hf03_eq_f2
      · exact False.elim (hf03_ne_f02 (hf03_eq_f1.trans hf02_eq_f1.symm))
      · exact hf03_eq_f2
    have hwit01_f03 :
        wit01 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f03.1 := by
      rw [hf03_eq_f2]
      decide
    have hwit01_erase :
        wit01 ∈
          (wheelWithInnerTriangleEmbedding.faceBoundary f03.1).erase
            (data.witnessEdge f03) := by
      refine Finset.mem_erase.2 ⟨?_, hwit01_f03⟩
      intro h
      exact wit01_ne_wit03 (h.trans hf03Witness)
    rcases data.hrest f03 hf03Peel wit01 hwit01_erase with
      hwit01Boundary | ⟨f01Next, hf01NextPeel, hf01NextWitness, hlt03_next⟩
    · exact wit01_not_mem_selectedBoundarySupport hwit01Boundary
    have hf01NextWitnessMem :
        data.witnessEdge f01Next ∈
          wheelWithInnerTriangleEmbedding.faceBoundary f01Next.1 :=
      data.hwitness f01Next hf01NextPeel
    have hwit01_f01Next :
        wit01 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f01Next.1 := by
      simpa [hf01NextWitness] using hf01NextWitnessMem
    have hf01Next_ne_f03 : f01Next ≠ f03 := by
      intro h
      subst h
      exact wit01_ne_wit03 (hf01NextWitness.symm.trans hf03Witness)
    have hf01Next_eq_f0 : f01Next = wheelFace0 := by
      rcases (wit01_mem_faceBoundary_iff f01Next).1 hwit01_f01Next with
        hf01Next_eq_f0 | hf01Next_eq_f2
      · exact hf01Next_eq_f0
      · exact False.elim (hf01Next_ne_f03 (hf01Next_eq_f2.trans hf03_eq_f2.symm))
    have hf01Next_eq_f01 : f01Next = f01 := hf01Next_eq_f0.trans hf01_eq_f0.symm
    have hloop : data.height f03 < data.height f01 := by
      simpa [hf01Next_eq_f01] using hlt03_next
    exact false_of_isChain_height_lt_and_getLast_lt_head
      data.height
      (cycle := [f01, f02, f03])
      (by simp)
      (by
        exact List.IsChain.cons_cons hlt01_02
          (List.IsChain.cons_cons hlt02_03 (by simp)))
      hloop
  · have hwit03_f01 :
        wit03 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f01.1 := by
      rw [hf01_eq_f2]
      decide
    have hwit03_erase :
        wit03 ∈
          (wheelWithInnerTriangleEmbedding.faceBoundary f01.1).erase
            (data.witnessEdge f01) := by
      refine Finset.mem_erase.2 ⟨?_, hwit03_f01⟩
      intro h
      exact wit01_ne_wit03 (hf01Witness.symm.trans h.symm)
    rcases data.hrest f01 hf01Peel wit03 hwit03_erase with
      hwit03Boundary | ⟨f03, hf03Peel, hf03Witness, hlt01_03⟩
    · exact wit03_not_mem_selectedBoundarySupport hwit03Boundary
    have hf03WitnessMem :
        data.witnessEdge f03 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f03.1 :=
      data.hwitness f03 hf03Peel
    have hwit03_f03 :
        wit03 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f03.1 := by
      simpa [hf03Witness] using hf03WitnessMem
    have hf03_ne_f01 : f03 ≠ f01 := by
      intro h
      subst h
      exact wit01_ne_wit03 (hf01Witness.symm.trans hf03Witness)
    have hf03_eq_f1 : f03 = wheelFace1 := by
      rcases (wit03_mem_faceBoundary_iff f03).1 hwit03_f03 with hf03_eq_f1 | hf03_eq_f2
      · exact hf03_eq_f1
      · exact False.elim (hf03_ne_f01 (hf03_eq_f2.trans hf01_eq_f2.symm))
    have hwit02_f03 :
        wit02 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f03.1 := by
      rw [hf03_eq_f1]
      decide
    have hwit02_erase :
        wit02 ∈
          (wheelWithInnerTriangleEmbedding.faceBoundary f03.1).erase
            (data.witnessEdge f03) := by
      refine Finset.mem_erase.2 ⟨?_, hwit02_f03⟩
      intro h
      exact wit02_ne_wit03 (h.trans hf03Witness)
    rcases data.hrest f03 hf03Peel wit02 hwit02_erase with
      hwit02Boundary | ⟨f02, hf02Peel, hf02Witness, hlt03_02⟩
    · exact wit02_not_mem_selectedBoundarySupport hwit02Boundary
    have hf02WitnessMem :
        data.witnessEdge f02 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f02.1 :=
      data.hwitness f02 hf02Peel
    have hwit02_f02 :
        wit02 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f02.1 := by
      simpa [hf02Witness] using hf02WitnessMem
    have hf02_ne_f03 : f02 ≠ f03 := by
      intro h
      subst h
      exact wit02_ne_wit03 (hf02Witness.symm.trans hf03Witness)
    have hf02_eq_f0 : f02 = wheelFace0 := by
      rcases (wit02_mem_faceBoundary_iff f02).1 hwit02_f02 with hf02_eq_f0 | hf02_eq_f1
      · exact hf02_eq_f0
      · exact False.elim (hf02_ne_f03 (hf02_eq_f1.trans hf03_eq_f1.symm))
    have hwit01_f02 :
        wit01 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f02.1 := by
      rw [hf02_eq_f0]
      decide
    have hwit01_erase :
        wit01 ∈
          (wheelWithInnerTriangleEmbedding.faceBoundary f02.1).erase
            (data.witnessEdge f02) := by
      refine Finset.mem_erase.2 ⟨?_, hwit01_f02⟩
      intro h
      exact wit01_ne_wit02 (h.trans hf02Witness)
    rcases data.hrest f02 hf02Peel wit01 hwit01_erase with
      hwit01Boundary | ⟨f01Next, hf01NextPeel, hf01NextWitness, hlt02_next⟩
    · exact wit01_not_mem_selectedBoundarySupport hwit01Boundary
    have hf01NextWitnessMem :
        data.witnessEdge f01Next ∈
          wheelWithInnerTriangleEmbedding.faceBoundary f01Next.1 :=
      data.hwitness f01Next hf01NextPeel
    have hwit01_f01Next :
        wit01 ∈ wheelWithInnerTriangleEmbedding.faceBoundary f01Next.1 := by
      simpa [hf01NextWitness] using hf01NextWitnessMem
    have hf01Next_ne_f02 : f01Next ≠ f02 := by
      intro h
      subst h
      exact wit01_ne_wit02 (hf01NextWitness.symm.trans hf02Witness)
    have hf01Next_eq_f2 : f01Next = wheelFace2 := by
      rcases (wit01_mem_faceBoundary_iff f01Next).1 hwit01_f01Next with
        hf01Next_eq_f0 | hf01Next_eq_f2
      · exact False.elim (hf01Next_ne_f02 (hf01Next_eq_f0.trans hf02_eq_f0.symm))
      · exact hf01Next_eq_f2
    have hf01Next_eq_f01 : f01Next = f01 := hf01Next_eq_f2.trans hf01_eq_f2.symm
    have hloop : data.height f02 < data.height f01 := by
      simpa [hf01Next_eq_f01] using hlt02_next
    exact false_of_isChain_height_lt_and_getLast_lt_head
      data.height
      (cycle := [f01, f03, f02])
      (by simp)
      (by
        exact List.IsChain.cons_cons hlt01_03
          (List.IsChain.cons_cons hlt03_02 (by simp)))
      hloop

/-- The same wheel dependency cycle also rules out the acyclic parent-peeling witness surface.
Any well-founded parent package has a canonical parent-height function, hence lowers to
height-ordered witness-cover data. -/
theorem not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle :
    ¬ Nonempty
        (PlanarBoundaryWellFoundedFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle
      ⟨data.toPlanarBoundaryHeightOrderedFacePeelWitnessData⟩

/-- The finite collar-layer replacement surface is also impossible on the wheel benchmark,
because collar-layer data lowers canonically to height-ordered witness-cover data. -/
theorem not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle :
    ¬ Nonempty
        (PlanarBoundaryCollarLayerFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle
      ⟨data.toHeightOrderedFacePeelWitnessData⟩

/-- The same height-cycle obstruction rules out weak annulus-collar geometry itself on this
fixed embedding, because any such collar geometry canonically lowers to height-ordered
witness-cover data. -/
theorem not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle :
    ¬ Nonempty
        (PlanarBoundaryAnnulusCollarGeometry wheelWithInnerTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle
      ⟨data.toPlanarBoundaryHeightOrderedFacePeelWitnessData⟩

/-- The repaired previous-boundary witness surface is also impossible on the wheel benchmark,
since it extends weak annulus-collar geometry. -/
theorem not_nonempty_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_wheelWithInnerTriangle :
    ¬ Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          wheelWithInnerTriangleEmbedding) := by
  rintro ⟨data⟩
  exact
    not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle
      ⟨data.toPlanarBoundaryAnnulusCollarGeometry⟩

/-- The same height-cycle obstruction blocks the current height-ordered positive replacement
geometry on the wheel benchmark.  The carrier is present, but the witness-cover datum required
by the replacement surface cannot exist. -/
theorem not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle :
    ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
        wheelWithInnerTriangleEmbedding := by
  exact
    not_heightOrderedPositiveProjectedGeometryOn_of_not_nonempty_heightOrderedFacePeelWitnessData
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle

/-- The finite-collar positive replacement geometry is impossible on the same benchmark for the
same reason: finite collars lower to the height-ordered witness-cover surface. -/
theorem not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle :
    ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
        wheelWithInnerTriangleEmbedding := by
  exact
    not_collarLayerPositiveProjectedGeometryOn_of_not_nonempty_collarLayerFacePeelWitnessData
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle

theorem wit12_mem_selectedBoundarySupport :
    wit12 ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit12⟩

theorem wit23_mem_selectedBoundarySupport :
    wit23 ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit23⟩

theorem wit31_mem_selectedBoundarySupport :
    wit31 ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit31⟩

theorem wit45_mem_selectedBoundarySupport :
    wit45 ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit45⟩

theorem wit56_mem_selectedBoundarySupport :
    wit56 ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit56⟩

theorem wit64_mem_selectedBoundarySupport :
    wit64 ∈ selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_wit64⟩

def wheelWithInnerTriangleEdgeColor
    (e : wheelWithInnerTriangleGraph.edgeSet) : Color :=
  if e = wit01 ∨ e = wit23 ∨ e = wit45 then red
  else if e = wit02 ∨ e = wit31 ∨ e = wit56 then blue
  else purple

@[simp] theorem wheelWithInnerTriangleEdgeColor_wit01 :
    wheelWithInnerTriangleEdgeColor wit01 = red := by
  simp [wheelWithInnerTriangleEdgeColor]

@[simp] theorem wheelWithInnerTriangleEdgeColor_wit02 :
    wheelWithInnerTriangleEdgeColor wit02 = blue := by
  simp [wheelWithInnerTriangleEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit23, wit45]

@[simp] theorem wheelWithInnerTriangleEdgeColor_wit03 :
    wheelWithInnerTriangleEdgeColor wit03 = purple := by
  simp [wheelWithInnerTriangleEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit03, wit23, wit31, wit45, wit56]

@[simp] theorem wheelWithInnerTriangleEdgeColor_wit12 :
    wheelWithInnerTriangleEdgeColor wit12 = purple := by
  simp [wheelWithInnerTriangleEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit12, wit23, wit31, wit45, wit56]

@[simp] theorem wheelWithInnerTriangleEdgeColor_wit23 :
    wheelWithInnerTriangleEdgeColor wit23 = red := by
  simp [wheelWithInnerTriangleEdgeColor, wheelWithInnerTriangleGraph, wit01, wit23]

@[simp] theorem wheelWithInnerTriangleEdgeColor_wit31 :
    wheelWithInnerTriangleEdgeColor wit31 = blue := by
  simp [wheelWithInnerTriangleEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit23, wit31, wit45]

@[simp] theorem wheelWithInnerTriangleEdgeColor_wit45 :
    wheelWithInnerTriangleEdgeColor wit45 = red := by
  simp [wheelWithInnerTriangleEdgeColor, wheelWithInnerTriangleGraph, wit01, wit23,
    wit45]

@[simp] theorem wheelWithInnerTriangleEdgeColor_wit56 :
    wheelWithInnerTriangleEdgeColor wit56 = blue := by
  simp [wheelWithInnerTriangleEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit23, wit31, wit45, wit56]

@[simp] theorem wheelWithInnerTriangleEdgeColor_wit64 :
    wheelWithInnerTriangleEdgeColor wit64 = purple := by
  simp [wheelWithInnerTriangleEdgeColor, wheelWithInnerTriangleGraph, wit01, wit02,
    wit23, wit31, wit45, wit56, wit64]

private theorem wheelWitness_blue_ne_red : blue ≠ red := by
  intro h
  exact red_ne_blue h.symm

private theorem wheelWitness_purple_ne_red : purple ≠ red := by
  intro h
  exact red_ne_purple h.symm

private theorem wheelWitness_purple_ne_blue : purple ≠ blue := by
  intro h
  exact blue_ne_purple h.symm

theorem wheelWithInnerTriangle_edge_mem_zero
    {e : wheelWithInnerTriangleGraph.edgeSet} (h : (0 : Fin 7) ∈ (e : Sym2 (Fin 7))) :
    e = wit01 ∨ e = wit02 ∨ e = wit03 := by
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelWithInnerTriangleGraph, wit01, wit02, wit03, wit12, wit23, wit31,
      wit45, wit56, wit64] at h ⊢

theorem wheelWithInnerTriangle_edge_mem_one
    {e : wheelWithInnerTriangleGraph.edgeSet} (h : (1 : Fin 7) ∈ (e : Sym2 (Fin 7))) :
    e = wit01 ∨ e = wit12 ∨ e = wit31 := by
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelWithInnerTriangleGraph, wit01, wit02, wit03, wit12, wit23, wit31,
      wit45, wit56, wit64] at h ⊢

theorem wheelWithInnerTriangle_edge_mem_two
    {e : wheelWithInnerTriangleGraph.edgeSet} (h : (2 : Fin 7) ∈ (e : Sym2 (Fin 7))) :
    e = wit02 ∨ e = wit12 ∨ e = wit23 := by
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelWithInnerTriangleGraph, wit01, wit02, wit03, wit12, wit23, wit31,
      wit45, wit56, wit64] at h ⊢

theorem wheelWithInnerTriangle_edge_mem_three
    {e : wheelWithInnerTriangleGraph.edgeSet} (h : (3 : Fin 7) ∈ (e : Sym2 (Fin 7))) :
    e = wit03 ∨ e = wit23 ∨ e = wit31 := by
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelWithInnerTriangleGraph, wit01, wit02, wit03, wit12, wit23, wit31,
      wit45, wit56, wit64] at h ⊢

theorem wheelWithInnerTriangle_edge_mem_four
    {e : wheelWithInnerTriangleGraph.edgeSet} (h : (4 : Fin 7) ∈ (e : Sym2 (Fin 7))) :
    e = wit45 ∨ e = wit64 := by
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelWithInnerTriangleGraph, wit01, wit02, wit03, wit12, wit23, wit31,
      wit45, wit56, wit64] at h ⊢

theorem wheelWithInnerTriangle_edge_mem_five
    {e : wheelWithInnerTriangleGraph.edgeSet} (h : (5 : Fin 7) ∈ (e : Sym2 (Fin 7))) :
    e = wit45 ∨ e = wit56 := by
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelWithInnerTriangleGraph, wit01, wit02, wit03, wit12, wit23, wit31,
      wit45, wit56, wit64] at h ⊢

theorem wheelWithInnerTriangle_edge_mem_six
    {e : wheelWithInnerTriangleGraph.edgeSet} (h : (6 : Fin 7) ∈ (e : Sym2 (Fin 7))) :
    e = wit56 ∨ e = wit64 := by
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelWithInnerTriangleGraph, wit01, wit02, wit03, wit12, wit23, wit31,
      wit45, wit56, wit64] at h ⊢

theorem wheelWithInnerTriangleEdgeColor_ne_of_adj
    {e f : wheelWithInnerTriangleGraph.edgeSet}
    (hadj : wheelWithInnerTriangleGraph.lineGraph.Adj e f) :
    wheelWithInnerTriangleEdgeColor e ≠ wheelWithInnerTriangleEdgeColor f := by
  intro hcolor
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  rcases hadj with ⟨hne, v, he, hf⟩
  fin_cases v
  · rcases wheelWithInnerTriangle_edge_mem_zero he with rfl | rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_zero hf with rfl | rfl | rfl <;>
      simp only [wheelWithInnerTriangleEdgeColor_wit01,
        wheelWithInnerTriangleEdgeColor_wit02, wheelWithInnerTriangleEdgeColor_wit03,
        red_ne_blue, red_ne_purple, blue_ne_purple, wheelWitness_blue_ne_red,
        wheelWitness_purple_ne_red, wheelWitness_purple_ne_blue, ne_eq, not_true_eq_false] at hne hcolor
  · rcases wheelWithInnerTriangle_edge_mem_one he with rfl | rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_one hf with rfl | rfl | rfl <;>
      simp only [wheelWithInnerTriangleEdgeColor_wit01,
        wheelWithInnerTriangleEdgeColor_wit12, wheelWithInnerTriangleEdgeColor_wit31,
        red_ne_blue, red_ne_purple, blue_ne_purple, wheelWitness_blue_ne_red,
        wheelWitness_purple_ne_red, wheelWitness_purple_ne_blue, ne_eq, not_true_eq_false] at hne hcolor
  · rcases wheelWithInnerTriangle_edge_mem_two he with rfl | rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_two hf with rfl | rfl | rfl <;>
      simp only [wheelWithInnerTriangleEdgeColor_wit02,
        wheelWithInnerTriangleEdgeColor_wit12, wheelWithInnerTriangleEdgeColor_wit23,
        red_ne_blue, red_ne_purple, blue_ne_purple, wheelWitness_blue_ne_red,
        wheelWitness_purple_ne_red, wheelWitness_purple_ne_blue, ne_eq, not_true_eq_false] at hne hcolor
  · rcases wheelWithInnerTriangle_edge_mem_three he with rfl | rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_three hf with rfl | rfl | rfl <;>
      simp only [wheelWithInnerTriangleEdgeColor_wit03,
        wheelWithInnerTriangleEdgeColor_wit23, wheelWithInnerTriangleEdgeColor_wit31,
        red_ne_blue, red_ne_purple, blue_ne_purple, wheelWitness_blue_ne_red,
        wheelWitness_purple_ne_red, wheelWitness_purple_ne_blue, ne_eq, not_true_eq_false] at hne hcolor
  · rcases wheelWithInnerTriangle_edge_mem_four he with rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_four hf with rfl | rfl <;>
      simp only [wheelWithInnerTriangleEdgeColor_wit45, wheelWithInnerTriangleEdgeColor_wit64,
        red_ne_purple, wheelWitness_purple_ne_red, ne_eq, not_true_eq_false] at hne hcolor
  · rcases wheelWithInnerTriangle_edge_mem_five he with rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_five hf with rfl | rfl <;>
      simp only [wheelWithInnerTriangleEdgeColor_wit45, wheelWithInnerTriangleEdgeColor_wit56,
        red_ne_blue, wheelWitness_blue_ne_red, ne_eq, not_true_eq_false] at hne hcolor
  · rcases wheelWithInnerTriangle_edge_mem_six he with rfl | rfl <;>
      rcases wheelWithInnerTriangle_edge_mem_six hf with rfl | rfl <;>
      simp only [wheelWithInnerTriangleEdgeColor_wit56, wheelWithInnerTriangleEdgeColor_wit64,
        blue_ne_purple, wheelWitness_purple_ne_blue, ne_eq, not_true_eq_false] at hne hcolor

def wheelWithInnerTriangleTaitEdgeColoring :
    wheelWithInnerTriangleGraph.EdgeColoring Color :=
  Coloring.mk wheelWithInnerTriangleEdgeColor (by
    intro e f hadj
    exact wheelWithInnerTriangleEdgeColor_ne_of_adj hadj)

theorem wheelWithInnerTriangleEdgeColor_ne_zero
    (e : wheelWithInnerTriangleGraph.edgeSet) :
    wheelWithInnerTriangleEdgeColor e ≠ 0 := by
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [wheelWithInnerTriangleEdgeColor_wit01,
      wheelWithInnerTriangleEdgeColor_wit02, wheelWithInnerTriangleEdgeColor_wit03,
      wheelWithInnerTriangleEdgeColor_wit12, wheelWithInnerTriangleEdgeColor_wit23,
      wheelWithInnerTriangleEdgeColor_wit31, wheelWithInnerTriangleEdgeColor_wit45,
      wheelWithInnerTriangleEdgeColor_wit56, wheelWithInnerTriangleEdgeColor_wit64] <;>
    first
    | exact red_ne_zero
    | exact blue_ne_zero
    | exact purple_ne_zero

theorem wheelWithInnerTriangleTaitEdgeColoring_isTait :
    IsTaitEdgeColoring wheelWithInnerTriangleGraph
      wheelWithInnerTriangleTaitEdgeColoring := by
  intro e
  exact wheelWithInnerTriangleEdgeColor_ne_zero e

theorem exists_taitEdgeColoring_wheelWithInnerTriangleGraph :
    ∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
      IsTaitEdgeColoring wheelWithInnerTriangleGraph C := by
  exact
    ⟨wheelWithInnerTriangleTaitEdgeColoring,
      wheelWithInnerTriangleTaitEdgeColoring_isTait⟩

theorem wheelWithInnerTriangle_boundaryEdge_eq
    (e : PlanarBoundaryEdgeVertex wheelWithInnerTriangleEmbedding) :
    e = ⟨wit12, wit12_mem_selectedBoundarySupport⟩ ∨
      e = ⟨wit23, wit23_mem_selectedBoundarySupport⟩ ∨
      e = ⟨wit31, wit31_mem_selectedBoundarySupport⟩ ∨
      e = ⟨wit45, wit45_mem_selectedBoundarySupport⟩ ∨
      e = ⟨wit56, wit56_mem_selectedBoundarySupport⟩ ∨
      e = ⟨wit64, wit64_mem_selectedBoundarySupport⟩ := by
  rcases wheelWithInnerTriangle_edge_eq e.1 with
    h01 | h02 | h03 | h12 | h23 | h31 | h45 | h56 | h64
  · exact False.elim (wit01_not_mem_selectedBoundarySupport (by simpa [h01] using e.2))
  · exact False.elim (wit02_not_mem_selectedBoundarySupport (by simpa [h02] using e.2))
  · exact False.elim (wit03_not_mem_selectedBoundarySupport (by simpa [h03] using e.2))
  · exact Or.inl (Subtype.ext h12)
  · exact Or.inr <| Or.inl (Subtype.ext h23)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h31)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h56)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext h64)

def wheelFace3 : AmbientFace wheelWithInnerTriangleEmbedding.faces :=
  ⟨(3 : WheelWithInnerTriangleFace), by
    simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaces]⟩

theorem wheelWithInnerTriangleFace_cases
    (f : AmbientFace wheelWithInnerTriangleEmbedding.faces) :
    f = wheelFace0 ∨ f = wheelFace1 ∨ f = wheelFace2 ∨ f = wheelFace3 := by
  rcases f with ⟨⟨n, hn⟩, hfmem⟩
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn_cases with rfl | rfl | rfl | rfl
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inr (Subtype.ext rfl)

def wheelDart01 : wheelWithInnerTriangleGraph.Dart := ⟨((0 : Fin 7), 1), by
  simp [wheelWithInnerTriangleGraph]⟩

def wheelDart10 : wheelWithInnerTriangleGraph.Dart := ⟨((1 : Fin 7), 0), by
  simp [wheelWithInnerTriangleGraph]⟩

def wheelDart02 : wheelWithInnerTriangleGraph.Dart := ⟨((0 : Fin 7), 2), by
  simp [wheelWithInnerTriangleGraph]⟩

def wheelDart20 : wheelWithInnerTriangleGraph.Dart := ⟨((2 : Fin 7), 0), by
  simp [wheelWithInnerTriangleGraph]⟩

def wheelDart03 : wheelWithInnerTriangleGraph.Dart := ⟨((0 : Fin 7), 3), by
  simp [wheelWithInnerTriangleGraph]⟩

def wheelDart30 : wheelWithInnerTriangleGraph.Dart := ⟨((3 : Fin 7), 0), by
  simp [wheelWithInnerTriangleGraph]⟩

def wheelDart12 : wheelWithInnerTriangleGraph.Dart := ⟨((1 : Fin 7), 2), by
  simp [wheelWithInnerTriangleGraph]⟩

def wheelDart23 : wheelWithInnerTriangleGraph.Dart := ⟨((2 : Fin 7), 3), by
  simp [wheelWithInnerTriangleGraph]⟩

def wheelDart31 : wheelWithInnerTriangleGraph.Dart := ⟨((3 : Fin 7), 1), by
  simp [wheelWithInnerTriangleGraph]⟩

def wheelDart45 : wheelWithInnerTriangleGraph.Dart := ⟨((4 : Fin 7), 5), by
  simp [wheelWithInnerTriangleGraph]⟩

def wheelDart56 : wheelWithInnerTriangleGraph.Dart := ⟨((5 : Fin 7), 6), by
  simp [wheelWithInnerTriangleGraph]⟩

def wheelDart64 : wheelWithInnerTriangleGraph.Dart := ⟨((6 : Fin 7), 4), by
  simp [wheelWithInnerTriangleGraph]⟩

def wheelFace0PureDartCycle
    (hf : (0 : WheelWithInnerTriangleFace) ∈ wheelWithInnerTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      wheelWithInnerTriangleEmbedding ⟨(0 : WheelWithInnerTriangleFace), hf⟩ where
  darts := [wheelDart01, wheelDart12, wheelDart20]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, wheelDart01, wheelDart12, wheelDart20]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary,
        wit01, wit12, wit02, wheelDart01, wheelDart12, wheelDart20]
  hface_sub := by
    intro e he
    have he' : e = wit01 ∨ e = wit02 ∨ e = wit12 := by
      simpa [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [wit01, wit02, wit12, wheelDart01, wheelDart12, wheelDart20]

def wheelFace1PureDartCycle
    (hf : (1 : WheelWithInnerTriangleFace) ∈ wheelWithInnerTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      wheelWithInnerTriangleEmbedding ⟨(1 : WheelWithInnerTriangleFace), hf⟩ where
  darts := [wheelDart02, wheelDart23, wheelDart30]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, wheelDart02, wheelDart23, wheelDart30]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary,
        wit02, wit23, wit03, wheelDart02, wheelDart23, wheelDart30]
  hface_sub := by
    intro e he
    have he' : e = wit02 ∨ e = wit03 ∨ e = wit23 := by
      simpa [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [wit02, wit03, wit23, wheelDart02, wheelDart23, wheelDart30]

def wheelFace2PureDartCycle
    (hf : (2 : WheelWithInnerTriangleFace) ∈ wheelWithInnerTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      wheelWithInnerTriangleEmbedding ⟨(2 : WheelWithInnerTriangleFace), hf⟩ where
  darts := [wheelDart03, wheelDart31, wheelDart10]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, wheelDart03, wheelDart31, wheelDart10]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary,
        wit03, wit31, wit01, wheelDart03, wheelDart31, wheelDart10]
  hface_sub := by
    intro e he
    have he' : e = wit03 ∨ e = wit01 ∨ e = wit31 := by
      simpa [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [wit03, wit01, wit31, wheelDart03, wheelDart31, wheelDart10]

def wheelFace3PureDartCycle
    (hf : (3 : WheelWithInnerTriangleFace) ∈ wheelWithInnerTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      wheelWithInnerTriangleEmbedding ⟨(3 : WheelWithInnerTriangleFace), hf⟩ where
  darts := [wheelDart45, wheelDart56, wheelDart64]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, wheelDart45, wheelDart56, wheelDart64]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary,
        wit45, wit56, wit64, wheelDart45, wheelDart56, wheelDart64]
  hface_sub := by
    intro e he
    have he' : e = wit45 ∨ e = wit56 ∨ e = wit64 := by
      simpa [wheelWithInnerTriangleEmbedding, wheelWithInnerTriangleFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [wit45, wit56, wit64, wheelDart45, wheelDart56, wheelDart64]

def wheelWithInnerTrianglePureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry
      wheelWithInnerTriangleEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change WheelWithInnerTriangleFace at f
    by_cases h0 : f = (0 : WheelWithInnerTriangleFace)
    · subst f
      exact wheelFace0PureDartCycle hfmem
    · by_cases h1 : f = (1 : WheelWithInnerTriangleFace)
      · subst f
        exact wheelFace1PureDartCycle hfmem
      · by_cases h2 : f = (2 : WheelWithInnerTriangleFace)
        · subst f
          exact wheelFace2PureDartCycle hfmem
        · have h3 : f = (3 : WheelWithInnerTriangleFace) := by
            rcases f with ⟨n, hn⟩
            have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
            rcases hn_cases with rfl | rfl | rfl | rfl
            · exact False.elim (h0 rfl)
            · exact False.elim (h1 rfl)
            · exact False.elim (h2 rfl)
            · rfl
          subst f
          exact wheelFace3PureDartCycle hfmem

def wheelFace0DartSuccessor (d : wheelWithInnerTriangleGraph.Dart) :
    wheelWithInnerTriangleGraph.Dart :=
  if d = wheelDart01 then wheelDart12
  else if d = wheelDart12 then wheelDart20
  else wheelDart01

def wheelFace1DartSuccessor (d : wheelWithInnerTriangleGraph.Dart) :
    wheelWithInnerTriangleGraph.Dart :=
  if d = wheelDart02 then wheelDart23
  else if d = wheelDart23 then wheelDart30
  else wheelDart02

def wheelFace2DartSuccessor (d : wheelWithInnerTriangleGraph.Dart) :
    wheelWithInnerTriangleGraph.Dart :=
  if d = wheelDart03 then wheelDart31
  else if d = wheelDart31 then wheelDart10
  else wheelDart03

def wheelFace3DartSuccessor (d : wheelWithInnerTriangleGraph.Dart) :
    wheelWithInnerTriangleGraph.Dart :=
  if d = wheelDart45 then wheelDart56
  else if d = wheelDart56 then wheelDart64
  else wheelDart45

def wheelFace0DartSuccessorCycle
    (hf : (0 : WheelWithInnerTriangleFace) ∈ wheelWithInnerTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      wheelWithInnerTriangleEmbedding ⟨(0 : WheelWithInnerTriangleFace), hf⟩ where
  darts := [wheelDart01, wheelDart12, wheelDart20]
  hnonempty := by simp
  successor := wheelFace0DartSuccessor
  hsuccessor_order := by
    simp [wheelFace0DartSuccessor, wheelDart01, wheelDart12, wheelDart20]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, wheelFace0DartSuccessor, wheelDart01, wheelDart12,
        wheelDart20]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (wheelFace0PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (wheelFace0PureDartCycle hf).hface_sub e he

def wheelFace1DartSuccessorCycle
    (hf : (1 : WheelWithInnerTriangleFace) ∈ wheelWithInnerTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      wheelWithInnerTriangleEmbedding ⟨(1 : WheelWithInnerTriangleFace), hf⟩ where
  darts := [wheelDart02, wheelDart23, wheelDart30]
  hnonempty := by simp
  successor := wheelFace1DartSuccessor
  hsuccessor_order := by
    simp [wheelFace1DartSuccessor, wheelDart02, wheelDart23, wheelDart30]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, wheelFace1DartSuccessor, wheelDart02, wheelDart23,
        wheelDart30]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (wheelFace1PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (wheelFace1PureDartCycle hf).hface_sub e he

def wheelFace2DartSuccessorCycle
    (hf : (2 : WheelWithInnerTriangleFace) ∈ wheelWithInnerTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      wheelWithInnerTriangleEmbedding ⟨(2 : WheelWithInnerTriangleFace), hf⟩ where
  darts := [wheelDart03, wheelDart31, wheelDart10]
  hnonempty := by simp
  successor := wheelFace2DartSuccessor
  hsuccessor_order := by
    simp [wheelFace2DartSuccessor, wheelDart03, wheelDart31, wheelDart10]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, wheelFace2DartSuccessor, wheelDart03, wheelDart31,
        wheelDart10]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (wheelFace2PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (wheelFace2PureDartCycle hf).hface_sub e he

def wheelFace3DartSuccessorCycle
    (hf : (3 : WheelWithInnerTriangleFace) ∈ wheelWithInnerTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      wheelWithInnerTriangleEmbedding ⟨(3 : WheelWithInnerTriangleFace), hf⟩ where
  darts := [wheelDart45, wheelDart56, wheelDart64]
  hnonempty := by simp
  successor := wheelFace3DartSuccessor
  hsuccessor_order := by
    simp [wheelFace3DartSuccessor, wheelDart45, wheelDart56, wheelDart64]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, wheelFace3DartSuccessor, wheelDart45, wheelDart56,
        wheelDart64]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (wheelFace3PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (wheelFace3PureDartCycle hf).hface_sub e he

def wheelWithInnerTriangleDartSuccessorCycleGeometry :
    PlanarBoundaryDartSuccessorCycleEmbeddingData wheelWithInnerTriangleEmbedding where
  faceBoundaryDartSuccessorCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change WheelWithInnerTriangleFace at f
    by_cases h0 : f = (0 : WheelWithInnerTriangleFace)
    · subst f
      exact wheelFace0DartSuccessorCycle hfmem
    · by_cases h1 : f = (1 : WheelWithInnerTriangleFace)
      · subst f
        exact wheelFace1DartSuccessorCycle hfmem
      · by_cases h2 : f = (2 : WheelWithInnerTriangleFace)
        · subst f
          exact wheelFace2DartSuccessorCycle hfmem
        · have h3 : f = (3 : WheelWithInnerTriangleFace) := by
            fin_cases f
            · exact False.elim (h0 rfl)
            · exact False.elim (h1 rfl)
            · exact False.elim (h2 rfl)
            · rfl
          subst f
          exact wheelFace3DartSuccessorCycle hfmem

theorem nonempty_wheelWithInnerTriangleDartSuccessorCycleGeometry :
    Nonempty
      (PlanarBoundaryDartSuccessorCycleEmbeddingData
        wheelWithInnerTriangleEmbedding) :=
  ⟨wheelWithInnerTriangleDartSuccessorCycleGeometry⟩

def wheelWithInnerTriangleClosedWalkEmbeddingData :
    PlanarBoundaryClosedWalkEmbeddingData wheelWithInnerTriangleEmbedding :=
  wheelWithInnerTrianglePureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

theorem wheelWithInnerTriangleClosedWalkEmbeddingData_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
      (wheelWithInnerTriangleClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f := by
  intro f
  rcases wheelWithInnerTriangleFace_cases f with rfl | rfl | rfl | rfl
  · refine ⟨[wit12], ?_, ?_⟩
    · decide
    · intro e
      rcases wheelWithInnerTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · refine ⟨[wit23], ?_, ?_⟩
    · decide
    · intro e
      rcases wheelWithInnerTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · refine ⟨[wit31], ?_, ?_⟩
    · decide
    · intro e
      rcases wheelWithInnerTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · refine ⟨[wit45, wit56, wit64], ?_, ?_⟩
    · decide
    · intro e
      rcases wheelWithInnerTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide

theorem wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
      (wheelWithInnerTriangleDartSuccessorCycleGeometry.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f := by
  intro f
  rcases wheelWithInnerTriangleFace_cases f with rfl | rfl | rfl | rfl
  · refine ⟨[wit12], ?_, ?_⟩
    · decide
    · intro e
      rcases wheelWithInnerTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · refine ⟨[wit23], ?_, ?_⟩
    · decide
    · intro e
      rcases wheelWithInnerTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · refine ⟨[wit31], ?_, ?_⟩
    · decide
    · intro e
      rcases wheelWithInnerTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · refine ⟨[wit45, wit56, wit64], ?_, ?_⟩
    · decide
    · intro e
      rcases wheelWithInnerTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide

def wheelOuterRoot : PlanarBoundaryEdgeVertex wheelWithInnerTriangleEmbedding :=
  ⟨wit12, wit12_mem_selectedBoundarySupport⟩

def wheelInnerRoot : PlanarBoundaryEdgeVertex wheelWithInnerTriangleEmbedding :=
  ⟨wit45, wit45_mem_selectedBoundarySupport⟩

theorem wheelOuterRoot_ne_innerRoot : wheelOuterRoot ≠ wheelInnerRoot := by
  intro h
  have := congrArg Subtype.val h
  simp [wheelOuterRoot, wheelInnerRoot, wit12, wit45] at this

def wheelBoundaryLabel
    (e : PlanarBoundaryEdgeVertex wheelWithInnerTriangleEmbedding) : Bool :=
  if e = ⟨wit12, wit12_mem_selectedBoundarySupport⟩ ∨
      e = ⟨wit23, wit23_mem_selectedBoundarySupport⟩ ∨
        e = ⟨wit31, wit31_mem_selectedBoundarySupport⟩ then
    false
  else
    true

theorem wheelBoundaryAdj_preserves_label :
    ∀ ⦃e f : PlanarBoundaryEdgeVertex wheelWithInnerTriangleEmbedding⦄,
      (planarBoundarySupportEndpointAdjGraph wheelWithInnerTriangleEmbedding).Adj e f →
        wheelBoundaryLabel e = wheelBoundaryLabel f := by
  intro e f hadj
  rcases wheelWithInnerTriangle_boundaryEdge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases wheelWithInnerTriangle_boundaryEdge_eq f with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact False.elim
          (by
            rcases hadj with ⟨_, v, hvE, hvF⟩
            fin_cases v <;>
              simp [wit12, wit23, wit31, wit45, wit56, wit64] at hvE hvF)

theorem wheel23_reachable_outerRoot :
    (planarBoundarySupportEndpointAdjGraph wheelWithInnerTriangleEmbedding).Reachable
      ⟨wit23, wit23_mem_selectedBoundarySupport⟩ wheelOuterRoot := by
  have hadj :
      (planarBoundarySupportEndpointAdjGraph wheelWithInnerTriangleEmbedding).Adj
        ⟨wit23, wit23_mem_selectedBoundarySupport⟩ wheelOuterRoot := by
    refine ⟨?_, 2, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp [wheelOuterRoot, wit23, wit12] at this
    · simp [wit23]
    · simp [wheelOuterRoot, wit12]
  exact hadj.reachable

theorem wheel31_reachable_outerRoot :
    (planarBoundarySupportEndpointAdjGraph wheelWithInnerTriangleEmbedding).Reachable
      ⟨wit31, wit31_mem_selectedBoundarySupport⟩ wheelOuterRoot := by
  have hadj :
      (planarBoundarySupportEndpointAdjGraph wheelWithInnerTriangleEmbedding).Adj
        ⟨wit31, wit31_mem_selectedBoundarySupport⟩ wheelOuterRoot := by
    refine ⟨?_, 1, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp [wheelOuterRoot, wit31, wit12] at this
    · simp [wit31]
    · simp [wheelOuterRoot, wit12]
  exact hadj.reachable

theorem wheel56_reachable_innerRoot :
    (planarBoundarySupportEndpointAdjGraph wheelWithInnerTriangleEmbedding).Reachable
      ⟨wit56, wit56_mem_selectedBoundarySupport⟩ wheelInnerRoot := by
  have hadj :
      (planarBoundarySupportEndpointAdjGraph wheelWithInnerTriangleEmbedding).Adj
        ⟨wit56, wit56_mem_selectedBoundarySupport⟩ wheelInnerRoot := by
    refine ⟨?_, 5, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp [wheelInnerRoot, wit56, wit45] at this
    · simp [wit56]
    · simp [wheelInnerRoot, wit45]
  exact hadj.reachable

theorem wheel64_reachable_innerRoot :
    (planarBoundarySupportEndpointAdjGraph wheelWithInnerTriangleEmbedding).Reachable
      ⟨wit64, wit64_mem_selectedBoundarySupport⟩ wheelInnerRoot := by
  have hadj :
      (planarBoundarySupportEndpointAdjGraph wheelWithInnerTriangleEmbedding).Adj
        ⟨wit64, wit64_mem_selectedBoundarySupport⟩ wheelInnerRoot := by
    refine ⟨?_, 4, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp [wheelInnerRoot, wit64, wit45] at this
    · simp [wit64]
    · simp [wheelInnerRoot, wit45]
  exact hadj.reachable

def wheelWithInnerTriangleAnnulusBoundaryReachabilityData :
    PlanarBoundaryAnnulusBoundaryReachabilityData wheelWithInnerTriangleEmbedding where
  outerRoot := wheelOuterRoot
  innerRoot := wheelInnerRoot
  hroots_ne := wheelOuterRoot_ne_innerRoot
  hcoverRoots := by
    intro e
    rcases wheelWithInnerTriangle_boundaryEdge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨wheelOuterRoot, by simp [wheelOuterRoot_ne_innerRoot],
        SimpleGraph.Reachable.refl _⟩
    · exact ⟨wheelOuterRoot, by simp [wheelOuterRoot_ne_innerRoot],
        wheel23_reachable_outerRoot⟩
    · exact ⟨wheelOuterRoot, by simp [wheelOuterRoot_ne_innerRoot],
        wheel31_reachable_outerRoot⟩
    · exact ⟨wheelInnerRoot, by simp, SimpleGraph.Reachable.refl _⟩
    · exact ⟨wheelInnerRoot, by simp, wheel56_reachable_innerRoot⟩
    · exact ⟨wheelInnerRoot, by simp, wheel64_reachable_innerRoot⟩
  hsepRoots := by
    intro r s hr hs hreach
    have hlabelEq :
        wheelBoundaryLabel r = wheelBoundaryLabel s :=
      eq_of_reachable_of_eq_on_adj
        (planarBoundarySupportEndpointAdjGraph wheelWithInnerTriangleEmbedding)
        wheelBoundaryLabel
        (by
          intro u v huv
          exact wheelBoundaryAdj_preserves_label huv)
        hreach
    have hOuterLabel : wheelBoundaryLabel wheelOuterRoot = false := by
      simp [wheelBoundaryLabel, wheelOuterRoot]
    have hInnerLabel : wheelBoundaryLabel wheelInnerRoot = true := by
      simp [wheelBoundaryLabel, wheelInnerRoot, wit12, wit23, wit31, wit45]
    have hr_cases : r = wheelOuterRoot ∨ r = wheelInnerRoot := by
      simpa [wheelOuterRoot_ne_innerRoot] using hr
    have hs_cases : s = wheelOuterRoot ∨ s = wheelInnerRoot := by
      simpa [wheelOuterRoot_ne_innerRoot] using hs
    rcases hr_cases with rfl | rfl <;> rcases hs_cases with rfl | rfl
    · rfl
    · rw [hOuterLabel, hInnerLabel] at hlabelEq
      cases hlabelEq
    · rw [hInnerLabel, hOuterLabel] at hlabelEq
      cases hlabelEq
    · rfl

def wheelWithInnerTriangleClosedWalkAnnulusBoundarySource :
    PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields
    wheelWithInnerTriangleAnnulusBoundaryReachabilityData
    wheelWithInnerTriangleClosedWalkEmbeddingData
    wheelWithInnerTriangleClosedWalkEmbeddingData_selectedBoundaryArcOnFace

def wheelWithInnerTriangleDartSuccessorClosedWalkAnnulusBoundarySource :
    PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
    wheelWithInnerTriangleAnnulusBoundaryReachabilityData
    wheelWithInnerTriangleDartSuccessorCycleGeometry
    wheelWithInnerTriangleDartSuccessorCycleGeometry_selectedBoundaryArcOnFace

theorem nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource :
    Nonempty
      (PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding) :=
  ⟨wheelWithInnerTriangleClosedWalkAnnulusBoundarySource⟩

theorem nonempty_wheelWithInnerTriangleDartSuccessorClosedWalkAnnulusBoundarySource :
    Nonempty
      (PlanarBoundaryClosedWalkAnnulusBoundarySource wheelWithInnerTriangleEmbedding) :=
  ⟨wheelWithInnerTriangleDartSuccessorClosedWalkAnnulusBoundarySource⟩

theorem vertex_zero_avoids_selectedBoundarySupport_wheelWithInnerTriangle :
    ∀ e ∈ selectedBoundarySupport
        wheelWithInnerTriangleEmbedding.faceBoundary
        wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces,
      (0 : Fin 7) ∉ (e : Sym2 (Fin 7)) := by
  intro e he
  rcases wheelWithInnerTriangle_boundaryEdge_eq ⟨e, he⟩ with
    h12 | h23 | h31 | h45 | h56 | h64
  · have heq : e = wit12 := congrArg Subtype.val h12
    subst e
    simp [wit12]
  · have heq : e = wit23 := congrArg Subtype.val h23
    subst e
    simp [wit23]
  · have heq : e = wit31 := congrArg Subtype.val h31
    subst e
    simp [wit31]
  · have heq : e = wit45 := congrArg Subtype.val h45
    subst e
    simp [wit45]
  · have heq : e = wit56 := congrArg Subtype.val h56
    subst e
    simp [wit56]
  · have heq : e = wit64 := congrArg Subtype.val h64
    subst e
    simp [wit64]

theorem vertex_zero_mem_selectedBoundaryInteriorEdgeEndpointVertices_wheelWithInnerTriangle :
    (0 : Fin 7) ∈
      selectedBoundaryInteriorEdgeEndpointVertices wheelWithInnerTriangleEmbedding := by
  rw [mem_selectedBoundaryInteriorEdgeEndpointVertices_iff]
  constructor
  · exact ⟨wit01, wit01_mem_interiorEdgeSupport, by simp [wit01]⟩
  · exact vertex_zero_avoids_selectedBoundarySupport_wheelWithInnerTriangle

theorem selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle :
    (selectedBoundaryInteriorEdgeEndpointVertices
      wheelWithInnerTriangleEmbedding).Nonempty := by
  refine
    (selectedBoundaryInteriorEdgeEndpointVertices_nonempty_iff_exists_unblocked_interior_endpoint
      wheelWithInnerTriangleEmbedding).2 ?_
  exact
    ⟨wit01, wit01_mem_interiorEdgeSupport, 0, by simp [wit01],
      vertex_zero_avoids_selectedBoundarySupport_wheelWithInnerTriangle⟩

/-- A compact constructive benchmark: unlike the explicit diamond benchmark, this finite model is
Tait-colorable and has a nonempty selected-boundary purified interior-edge endpoint carrier on
the same concrete boundary embedding. -/
theorem wheelWithInnerTriangle_tait_and_nonempty_selectedBoundaryInteriorCarrier :
    IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty := by
  exact
    ⟨wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle⟩

/-- The wheel benchmark has the desired Tait coloring and purified carrier, but the same concrete
face geometry blocks the canonical witness-choice and one-collar routes. -/
theorem wheelWithInnerTriangle_tait_and_nonempty_carrier_without_canonical_or_oneCollar :
    IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      (∀ boundaryData : PlanarBoundaryAnnulusBoundaryData wheelWithInnerTriangleEmbedding,
        ¬ Nonempty (PlanarBoundaryCanonicalWitnessChoice boundaryData)) ∧
      ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 := by
  exact
    ⟨wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCanonicalWitnessChoice_wheelWithInnerTriangle,
      not_exists_oneCollar_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle⟩

/-- Sharper wheel calibration after the at-most-one sufficient condition was added: this model
still supplies the desired Tait coloring and nonempty purified endpoint carrier, but the same
embedding fails the at-most-one local premise, every annulus boundary split blocks canonical
witness choice, and no one-collar geometry exists. -/
theorem
    wheelWithInnerTriangle_tait_and_nonempty_carrier_without_atMostOne_or_canonical_or_oneCollar :
    IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      (¬ ∀ f : AmbientFace wheelWithInnerTriangleEmbedding.faces,
        ((wheelWithInnerTriangleEmbedding.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport wheelWithInnerTriangleEmbedding.faceBoundary
              wheelWithInnerTriangleEmbedding.faces)).card ≤ 1) ∧
      (∀ boundaryData : PlanarBoundaryAnnulusBoundaryData wheelWithInnerTriangleEmbedding,
        ¬ Nonempty (PlanarBoundaryCanonicalWitnessChoice boundaryData)) ∧
      ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry wheelWithInnerTriangleEmbedding,
        data.numCollars = 1 := by
  exact
    ⟨wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      not_wheelWithInnerTriangle_atMostOneInteriorEdgePerFace,
      not_nonempty_planarBoundaryCanonicalWitnessChoice_wheelWithInnerTriangle,
      not_exists_oneCollar_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle⟩

/-- Sharper same-embedding calibration: the wheel benchmark has a Tait coloring and a nonempty
purified carrier, but none of the current witness-cover or weak annulus-collar geometry endpoints
can exist on this embedding. -/
theorem
    wheelWithInnerTriangle_tait_and_nonempty_carrier_without_witnessCover_or_annulusCollarGeometry :
    IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryCollarLayerFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusCollarGeometry wheelWithInnerTriangleEmbedding) := by
  exact
    ⟨wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle⟩

/-- The sharpened acyclic form: the same coloring and carrier data coexist with failure of the
well-founded, height-ordered, finite-collar, and weak annulus-collar geometric endpoints. -/
theorem
    wheelWithInnerTriangle_tait_and_nonempty_carrier_without_acyclicWitnessCover_or_annulusCollarGeometry :
    IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      ¬ Nonempty
        (PlanarBoundaryWellFoundedFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryCollarLayerFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusCollarGeometry wheelWithInnerTriangleEmbedding) := by
  exact
    ⟨wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle⟩

/-- Source-bearing acyclic calibration: the wheel benchmark carries an honest closed-walk annulus
source, a Tait coloring, and a nonempty purified carrier, but no current acyclic witness-cover or
weak annulus-collar endpoint exists on the same embedding. -/
theorem
    wheelWithInnerTriangle_closedWalkSource_tait_and_nonempty_carrier_without_acyclicWitnessCover_or_annulusCollarGeometry :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource
          wheelWithInnerTriangleEmbedding) ∧
      IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      ¬ Nonempty
        (PlanarBoundaryWellFoundedFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryCollarLayerFacePeelWitnessData
          wheelWithInnerTriangleEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusCollarGeometry wheelWithInnerTriangleEmbedding) := by
  exact
    ⟨nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle⟩

/-- Direct replacement calibration: the wheel benchmark carries an honest closed-walk annulus
source, a Tait coloring, and the purified carrier, but the strict height cycle blocks both
current positive replacement packages and the repaired previous-boundary annulus geometry on the
same embedding. -/
theorem
    wheelWithInnerTriangle_closedWalkSource_tait_and_nonempty_carrier_without_replacementPositiveProjectedGeometry_or_previousBoundaryWitness :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource
          wheelWithInnerTriangleEmbedding) ∧
      IsTaitEdgeColoring wheelWithInnerTriangleGraph
        wheelWithInnerTriangleTaitEdgeColoring ∧
      (selectedBoundaryInteriorEdgeEndpointVertices
        wheelWithInnerTriangleEmbedding).Nonempty ∧
      ¬ Theorem49HeightOrderedPositiveProjectedGeometryOn
        wheelWithInnerTriangleEmbedding ∧
      ¬ Theorem49CollarLayerPositiveProjectedGeometryOn
        wheelWithInnerTriangleEmbedding ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          wheelWithInnerTriangleEmbedding) := by
  exact
    ⟨nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource,
      wheelWithInnerTriangleTaitEdgeColoring_isTait,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle,
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle,
      not_nonempty_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_wheelWithInnerTriangle⟩

/-- Tait colorability plus a nonempty purified selected-boundary interior carrier does not
universally construct any of the current same-embedding witness-cover or weak annulus-collar
geometric endpoints.  The fixed wheel embedding supplies the counterexample. -/
theorem
    not_forall_some_witnessCover_or_annulusCollarGeometry_of_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        (∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C) →
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
            Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  have hAny :=
    h wheelWithInnerTriangleEmbedding
      exists_taitEdgeColoring_wheelWithInnerTriangleGraph
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
  rcases hAny with hHeight | hCollar | hAnnulus
  · exact
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle
        hHeight
  · exact
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle
        hCollar
  · exact
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle
        hAnnulus

/-- Even for honest closed-walk source data, Tait colorability, and the purified carrier, one
cannot universally construct either direct positive replacement geometry or the repaired
previous-boundary annulus geometry.  The wheel benchmark satisfies the hypotheses while its
three-spoke height cycle blocks all three conclusions. -/
theorem
    not_forall_some_replacementPositiveProjectedGeometry_or_previousBoundaryWitness_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C) →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
              Theorem49HeightOrderedPositiveProjectedGeometryOn emb ∨
                Theorem49CollarLayerPositiveProjectedGeometryOn emb ∨
                  Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) := by
  intro h
  have hAny :=
    h wheelWithInnerTriangleEmbedding
      nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
      exists_taitEdgeColoring_wheelWithInnerTriangleGraph
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
  rcases hAny with hHeight | hCollar | hPrevious
  · exact
      not_theorem49HeightOrderedPositiveProjectedGeometryOn_wheelWithInnerTriangle
        hHeight
  · exact
      not_theorem49CollarLayerPositiveProjectedGeometryOn_wheelWithInnerTriangle
        hCollar
  · exact
      not_nonempty_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_wheelWithInnerTriangle
        hPrevious

/-- Even an honest closed-walk annulus source, Tait colorability, and a nonempty purified carrier
do not universally construct any current acyclic witness-cover or weak annulus-collar endpoint.
The wheel benchmark has all three hypotheses while the three-spoke dependency cycle blocks every
one of the current geometric endpoints. -/
theorem
    not_forall_some_acyclicWitnessCover_or_annulusCollarGeometry_of_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          (∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring wheelWithInnerTriangleGraph C) →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                  Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                    Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  have hAny :=
    h wheelWithInnerTriangleEmbedding
      nonempty_wheelWithInnerTriangleClosedWalkAnnulusBoundarySource
      exists_taitEdgeColoring_wheelWithInnerTriangleGraph
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
  rcases hAny with hWellFounded | hHeight | hCollar | hAnnulus
  · exact
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle
        hWellFounded
  · exact
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle
        hHeight
  · exact
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle
        hCollar
  · exact
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle
        hAnnulus

/-- Even adding the acyclic parent-peeling endpoint to the conclusion does not make the universal
construction true: the wheel benchmark still satisfies the coloring and carrier hypotheses while
blocking every current same-embedding witness-cover or weak annulus-collar endpoint. -/
theorem
    not_forall_some_acyclicWitnessCover_or_annulusCollarGeometry_of_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_wheelWithInnerTriangle :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary wheelWithInnerTriangleGraph,
        (∃ C : wheelWithInnerTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring wheelWithInnerTriangleGraph C) →
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
            Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
                  Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  have hAny :=
    h wheelWithInnerTriangleEmbedding
      exists_taitEdgeColoring_wheelWithInnerTriangleGraph
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_wheelWithInnerTriangle
  rcases hAny with hWellFounded | hHeight | hCollar | hAnnulus
  · exact
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_wheelWithInnerTriangle
        hWellFounded
  · exact
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_wheelWithInnerTriangle
        hHeight
  · exact
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_wheelWithInnerTriangle
        hCollar
  · exact
      not_nonempty_planarBoundaryAnnulusCollarGeometry_wheelWithInnerTriangle
        hAnnulus

end Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

end Mettapedia.GraphTheory.FourColor
