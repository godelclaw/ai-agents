import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusRootInteriorDual
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceRoute
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49ForcingInteriorEdgeObstruction

namespace Theorem49PlanarBoundaryAnnulusRootInteriorDualObstructionRegression

/-- A concrete two-band annulus source.  Vertices `0,1,2` are the outer boundary,
`3,4,5` are the middle cycle, and `6,7,8` are the inner boundary.  The six
quadrilateral faces form a triangular strip between the outer and inner boundary cycles. -/
def twoBandAnnulusGraph : SimpleGraph (Fin 9) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 0),
        s(3, 4), s(4, 5), s(5, 3),
        s(6, 7), s(7, 8), s(8, 6),
        s(0, 3), s(1, 4), s(2, 5),
        s(3, 6), s(4, 7), s(5, 8)} : Set (Sym2 (Fin 9)))

def tbaO01 : twoBandAnnulusGraph.edgeSet := ⟨s(0, 1), by
  simp [twoBandAnnulusGraph]⟩

def tbaO12 : twoBandAnnulusGraph.edgeSet := ⟨s(1, 2), by
  simp [twoBandAnnulusGraph]⟩

def tbaO20 : twoBandAnnulusGraph.edgeSet := ⟨s(2, 0), by
  simp [twoBandAnnulusGraph]⟩

def tbaM01 : twoBandAnnulusGraph.edgeSet := ⟨s(3, 4), by
  simp [twoBandAnnulusGraph]⟩

def tbaM12 : twoBandAnnulusGraph.edgeSet := ⟨s(4, 5), by
  simp [twoBandAnnulusGraph]⟩

def tbaM20 : twoBandAnnulusGraph.edgeSet := ⟨s(5, 3), by
  simp [twoBandAnnulusGraph]⟩

def tbaI01 : twoBandAnnulusGraph.edgeSet := ⟨s(6, 7), by
  simp [twoBandAnnulusGraph]⟩

def tbaI12 : twoBandAnnulusGraph.edgeSet := ⟨s(7, 8), by
  simp [twoBandAnnulusGraph]⟩

def tbaI20 : twoBandAnnulusGraph.edgeSet := ⟨s(8, 6), by
  simp [twoBandAnnulusGraph]⟩

def tbaR0 : twoBandAnnulusGraph.edgeSet := ⟨s(0, 3), by
  simp [twoBandAnnulusGraph]⟩

def tbaR1 : twoBandAnnulusGraph.edgeSet := ⟨s(1, 4), by
  simp [twoBandAnnulusGraph]⟩

def tbaR2 : twoBandAnnulusGraph.edgeSet := ⟨s(2, 5), by
  simp [twoBandAnnulusGraph]⟩

def tbaS0 : twoBandAnnulusGraph.edgeSet := ⟨s(3, 6), by
  simp [twoBandAnnulusGraph]⟩

def tbaS1 : twoBandAnnulusGraph.edgeSet := ⟨s(4, 7), by
  simp [twoBandAnnulusGraph]⟩

def tbaS2 : twoBandAnnulusGraph.edgeSet := ⟨s(5, 8), by
  simp [twoBandAnnulusGraph]⟩

theorem twoBandAnnulus_edge_eq
    (e : twoBandAnnulusGraph.edgeSet) :
    e = tbaO01 ∨ e = tbaO12 ∨ e = tbaO20 ∨
      e = tbaM01 ∨ e = tbaM12 ∨ e = tbaM20 ∨
      e = tbaI01 ∨ e = tbaI12 ∨ e = tbaI20 ∨
      e = tbaR0 ∨ e = tbaR1 ∨ e = tbaR2 ∨
      e = tbaS0 ∨ e = tbaS1 ∨ e = tbaS2 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 0) ∨
          e.1 = s(3, 4) ∨ e.1 = s(4, 5) ∨ e.1 = s(5, 3) ∨
          e.1 = s(6, 7) ∨ e.1 = s(7, 8) ∨ e.1 = s(8, 6) ∨
          e.1 = s(0, 3) ∨ e.1 = s(1, 4) ∨ e.1 = s(2, 5) ∨
          e.1 = s(3, 6) ∨ e.1 = s(4, 7) ∨ e.1 = s(5, 8)) ∧
        ¬ e.1.IsDiag := by
    simpa [twoBandAnnulusGraph] using e.2
  rcases h.1 with h01 | h12 | h20 | hm01 | hm12 | hm20 | hi01 | hi12 | hi20 |
      hr0 | hr1 | hr2 | hs0 | hs1 | hs2
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr <| Or.inl (Subtype.ext h12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hm01)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hm12)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hm20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext hi01)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext hi12)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inl (Subtype.ext hi20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hr0)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hr1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hr2)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        (Subtype.ext hs0)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        (Subtype.ext hs1)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
        (Subtype.ext hs2)

abbrev TwoBandAnnulusFace := Fin 6

def twoBandAnnulusFaces : Finset TwoBandAnnulusFace := Finset.univ

def twoBandAnnulusFaceBoundary :
    TwoBandAnnulusFace → Finset twoBandAnnulusGraph.edgeSet
  | ⟨0, _⟩ => {tbaO01, tbaR1, tbaM01, tbaR0}
  | ⟨1, _⟩ => {tbaO12, tbaR2, tbaM12, tbaR1}
  | ⟨2, _⟩ => {tbaO20, tbaR0, tbaM20, tbaR2}
  | ⟨3, _⟩ => {tbaM01, tbaS1, tbaI01, tbaS0}
  | ⟨4, _⟩ => {tbaM12, tbaS2, tbaI12, tbaS1}
  | ⟨5, _⟩ => {tbaM20, tbaS0, tbaI20, tbaS2}

theorem totalIncidenceCount_tbaO01 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaO01 = 1 := by
  decide

theorem totalIncidenceCount_tbaO12 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaO12 = 1 := by
  decide

theorem totalIncidenceCount_tbaO20 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaO20 = 1 := by
  decide

theorem totalIncidenceCount_tbaM01 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaM01 = 2 := by
  decide

theorem totalIncidenceCount_tbaM12 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaM12 = 2 := by
  decide

theorem totalIncidenceCount_tbaM20 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaM20 = 2 := by
  decide

theorem totalIncidenceCount_tbaI01 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaI01 = 1 := by
  decide

theorem totalIncidenceCount_tbaI12 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaI12 = 1 := by
  decide

theorem totalIncidenceCount_tbaI20 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaI20 = 1 := by
  decide

theorem totalIncidenceCount_tbaR0 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaR0 = 2 := by
  decide

theorem totalIncidenceCount_tbaR1 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaR1 = 2 := by
  decide

theorem totalIncidenceCount_tbaR2 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaR2 = 2 := by
  decide

theorem totalIncidenceCount_tbaS0 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaS0 = 2 := by
  decide

theorem totalIncidenceCount_tbaS1 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaS1 = 2 := by
  decide

theorem totalIncidenceCount_tbaS2 :
    totalIncidenceCount twoBandAnnulusFaceBoundary twoBandAnnulusFaces tbaS2 = 2 := by
  decide

def twoBandAnnulusEmbedding : PlaneEmbeddingWithBoundary twoBandAnnulusGraph where
  Face := TwoBandAnnulusFace
  faceDecidableEq := inferInstance
  faces := twoBandAnnulusFaces
  faceBoundary := twoBandAnnulusFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases twoBandAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases twoBandAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
      decide

def twoBandOuterFace0 : AmbientFace twoBandAnnulusEmbedding.faces :=
  ⟨(0 : TwoBandAnnulusFace), by
    simp [twoBandAnnulusEmbedding, twoBandAnnulusFaces]⟩

def twoBandInnerFace0 : AmbientFace twoBandAnnulusEmbedding.faces :=
  ⟨(3 : TwoBandAnnulusFace), by
    simp [twoBandAnnulusEmbedding, twoBandAnnulusFaces]⟩

theorem tbaO01_mem_selectedBoundarySupport :
    tbaO01 ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, by simpa [twoBandAnnulusEmbedding] using totalIncidenceCount_tbaO01⟩

theorem tbaO12_mem_selectedBoundarySupport :
    tbaO12 ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, by simpa [twoBandAnnulusEmbedding] using totalIncidenceCount_tbaO12⟩

theorem tbaO20_mem_selectedBoundarySupport :
    tbaO20 ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, by simpa [twoBandAnnulusEmbedding] using totalIncidenceCount_tbaO20⟩

theorem tbaI01_mem_selectedBoundarySupport :
    tbaI01 ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, by simpa [twoBandAnnulusEmbedding] using totalIncidenceCount_tbaI01⟩

theorem tbaI12_mem_selectedBoundarySupport :
    tbaI12 ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, by simpa [twoBandAnnulusEmbedding] using totalIncidenceCount_tbaI12⟩

theorem tbaI20_mem_selectedBoundarySupport :
    tbaI20 ∈ selectedBoundarySupport
      twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces
      twoBandAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, by simpa [twoBandAnnulusEmbedding] using totalIncidenceCount_tbaI20⟩

theorem tbaM01_mem_interiorEdgeSupport :
    tbaM01 ∈ interiorEdgeSupport twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, by simpa [twoBandAnnulusEmbedding] using totalIncidenceCount_tbaM01⟩

theorem tbaM12_mem_interiorEdgeSupport :
    tbaM12 ∈ interiorEdgeSupport twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, by simpa [twoBandAnnulusEmbedding] using totalIncidenceCount_tbaM12⟩

theorem tbaM20_mem_interiorEdgeSupport :
    tbaM20 ∈ interiorEdgeSupport twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, by simpa [twoBandAnnulusEmbedding] using totalIncidenceCount_tbaM20⟩

def twoBandOuterRoot : PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding :=
  ⟨tbaO01, tbaO01_mem_selectedBoundarySupport⟩

def twoBandInnerRoot : PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding :=
  ⟨tbaI01, tbaI01_mem_selectedBoundarySupport⟩

def twoBandBoundaryLabel
    (e : PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding) : Bool :=
  if e.1 = tbaI01 ∨ e.1 = tbaI12 ∨ e.1 = tbaI20 then true else false

theorem twoBandBoundaryEdge_eq
    (e : PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding) :
    e = ⟨tbaO01, tbaO01_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tbaO12, tbaO12_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tbaO20, tbaO20_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tbaI01, tbaI01_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tbaI12, tbaI12_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tbaI20, tbaI20_mem_selectedBoundarySupport⟩ := by
  rcases twoBandAnnulus_edge_eq e.1 with
    hO01 | hO12 | hO20 | hM01 | hM12 | hM20 | hI01 | hI12 | hI20 | hR0 | hR1 |
      hR2 | hS0 | hS1 | hS2
  · exact Or.inl (Subtype.ext hO01)
  · exact Or.inr <| Or.inl (Subtype.ext hO12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext hO20)
  · exfalso
    have hcount :
        totalIncidenceCount twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces tbaM01 = 1 :=
      (mem_selectedBoundarySupport_iff twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces).1
        (by simpa [hM01] using e.2) |>.2
    simp [twoBandAnnulusEmbedding, totalIncidenceCount_tbaM01] at hcount
  · exfalso
    have hcount :
        totalIncidenceCount twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces tbaM12 = 1 :=
      (mem_selectedBoundarySupport_iff twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces).1
        (by simpa [hM12] using e.2) |>.2
    simp [twoBandAnnulusEmbedding, totalIncidenceCount_tbaM12] at hcount
  · exfalso
    have hcount :
        totalIncidenceCount twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces tbaM20 = 1 :=
      (mem_selectedBoundarySupport_iff twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces).1
        (by simpa [hM20] using e.2) |>.2
    simp [twoBandAnnulusEmbedding, totalIncidenceCount_tbaM20] at hcount
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI01)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext hI12)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext hI20)
  · exfalso
    have hcount :
        totalIncidenceCount twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces tbaR0 = 1 :=
      (mem_selectedBoundarySupport_iff twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces).1
        (by simpa [hR0] using e.2) |>.2
    simp [twoBandAnnulusEmbedding, totalIncidenceCount_tbaR0] at hcount
  · exfalso
    have hcount :
        totalIncidenceCount twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces tbaR1 = 1 :=
      (mem_selectedBoundarySupport_iff twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces).1
        (by simpa [hR1] using e.2) |>.2
    simp [twoBandAnnulusEmbedding, totalIncidenceCount_tbaR1] at hcount
  · exfalso
    have hcount :
        totalIncidenceCount twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces tbaR2 = 1 :=
      (mem_selectedBoundarySupport_iff twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces).1
        (by simpa [hR2] using e.2) |>.2
    simp [twoBandAnnulusEmbedding, totalIncidenceCount_tbaR2] at hcount
  · exfalso
    have hcount :
        totalIncidenceCount twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces tbaS0 = 1 :=
      (mem_selectedBoundarySupport_iff twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces).1
        (by simpa [hS0] using e.2) |>.2
    simp [twoBandAnnulusEmbedding, totalIncidenceCount_tbaS0] at hcount
  · exfalso
    have hcount :
        totalIncidenceCount twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces tbaS1 = 1 :=
      (mem_selectedBoundarySupport_iff twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces).1
        (by simpa [hS1] using e.2) |>.2
    simp [twoBandAnnulusEmbedding, totalIncidenceCount_tbaS1] at hcount
  · exfalso
    have hcount :
        totalIncidenceCount twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces tbaS2 = 1 :=
      (mem_selectedBoundarySupport_iff twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces).1
        (by simpa [hS2] using e.2) |>.2
    simp [twoBandAnnulusEmbedding, totalIncidenceCount_tbaS2] at hcount

theorem twoBandBoundaryAdj_preserves_label :
    ∀ ⦃e f : PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding⦄,
      (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Adj e f →
        twoBandBoundaryLabel e = twoBandBoundaryLabel f := by
  intro e f hadj
  rcases twoBandBoundaryEdge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases twoBandBoundaryEdge_eq f with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact False.elim
          (by
            rcases hadj with ⟨_, v, hvE, hvF⟩
            fin_cases v <;>
              simp [tbaO01, tbaO12, tbaO20, tbaI01, tbaI12, tbaI20] at hvE hvF)

theorem twoBandOuterRoot_ne_innerRoot :
    twoBandOuterRoot ≠ twoBandInnerRoot := by
  intro h
  have := congrArg Subtype.val h
  simp [twoBandOuterRoot, twoBandInnerRoot, tbaO01, tbaI01] at this

theorem twoBandO12_reachable_outerRoot :
    (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Reachable
      ⟨tbaO12, tbaO12_mem_selectedBoundarySupport⟩ twoBandOuterRoot := by
  have hadj :
      (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Adj
        ⟨tbaO12, tbaO12_mem_selectedBoundarySupport⟩ twoBandOuterRoot := by
    refine ⟨?_, 1, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp [twoBandOuterRoot, tbaO12, tbaO01] at this
    · simp [tbaO12]
    · simp [twoBandOuterRoot, tbaO01]
  exact hadj.reachable

theorem twoBandO20_reachable_outerRoot :
    (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Reachable
      ⟨tbaO20, tbaO20_mem_selectedBoundarySupport⟩ twoBandOuterRoot := by
  have hadj :
      (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Adj
        ⟨tbaO20, tbaO20_mem_selectedBoundarySupport⟩ twoBandOuterRoot := by
    refine ⟨?_, 0, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp [twoBandOuterRoot, tbaO20, tbaO01] at this
    · simp [tbaO20]
    · simp [twoBandOuterRoot, tbaO01]
  exact hadj.reachable

theorem twoBandI12_reachable_innerRoot :
    (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Reachable
      ⟨tbaI12, tbaI12_mem_selectedBoundarySupport⟩ twoBandInnerRoot := by
  have hadj :
      (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Adj
        ⟨tbaI12, tbaI12_mem_selectedBoundarySupport⟩ twoBandInnerRoot := by
    refine ⟨?_, 7, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp [twoBandInnerRoot, tbaI12, tbaI01] at this
    · simp [tbaI12]
    · simp [twoBandInnerRoot, tbaI01]
  exact hadj.reachable

theorem twoBandI20_reachable_innerRoot :
    (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Reachable
      ⟨tbaI20, tbaI20_mem_selectedBoundarySupport⟩ twoBandInnerRoot := by
  have hadj :
      (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding).Adj
        ⟨tbaI20, tbaI20_mem_selectedBoundarySupport⟩ twoBandInnerRoot := by
    refine ⟨?_, 6, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp [twoBandInnerRoot, tbaI20, tbaI01] at this
    · simp [tbaI20]
    · simp [twoBandInnerRoot, tbaI01]
  exact hadj.reachable

def twoBandAnnulusBoundaryReachabilityData :
    PlanarBoundaryAnnulusBoundaryReachabilityData twoBandAnnulusEmbedding where
  outerRoot := twoBandOuterRoot
  innerRoot := twoBandInnerRoot
  hroots_ne := twoBandOuterRoot_ne_innerRoot
  hcoverRoots := by
    intro e
    rcases twoBandBoundaryEdge_eq e with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨twoBandOuterRoot, by simp [twoBandOuterRoot_ne_innerRoot],
        SimpleGraph.Reachable.refl _⟩
    · exact ⟨twoBandOuterRoot, by simp [twoBandOuterRoot_ne_innerRoot],
        twoBandO12_reachable_outerRoot⟩
    · exact ⟨twoBandOuterRoot, by simp [twoBandOuterRoot_ne_innerRoot],
        twoBandO20_reachable_outerRoot⟩
    · exact ⟨twoBandInnerRoot, by simp, SimpleGraph.Reachable.refl _⟩
    · exact ⟨twoBandInnerRoot, by simp, twoBandI12_reachable_innerRoot⟩
    · exact ⟨twoBandInnerRoot, by simp, twoBandI20_reachable_innerRoot⟩
  hsepRoots := by
    intro r s hr hs hreach
    have hlabelEq :
        twoBandBoundaryLabel r = twoBandBoundaryLabel s :=
      eq_of_reachable_of_eq_on_adj
        (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
        twoBandBoundaryLabel
        (by
          intro u v huv
          exact twoBandBoundaryAdj_preserves_label huv)
        hreach
    have hOuterLabel : twoBandBoundaryLabel twoBandOuterRoot = false := by
      decide
    have hInnerLabel : twoBandBoundaryLabel twoBandInnerRoot = true := by
      decide
    have hr_cases : r = twoBandOuterRoot ∨ r = twoBandInnerRoot := by
      simpa [twoBandOuterRoot_ne_innerRoot] using hr
    have hs_cases : s = twoBandOuterRoot ∨ s = twoBandInnerRoot := by
      simpa [twoBandOuterRoot_ne_innerRoot] using hs
    rcases hr_cases with rfl | rfl <;> rcases hs_cases with rfl | rfl
    · rfl
    · rw [hOuterLabel, hInnerLabel] at hlabelEq
      cases hlabelEq
    · rw [hInnerLabel, hOuterLabel] at hlabelEq
      cases hlabelEq
    · rfl

def tbaDart01 : twoBandAnnulusGraph.Dart := ⟨((0 : Fin 9), 1), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart14 : twoBandAnnulusGraph.Dart := ⟨((1 : Fin 9), 4), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart43 : twoBandAnnulusGraph.Dart := ⟨((4 : Fin 9), 3), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart30 : twoBandAnnulusGraph.Dart := ⟨((3 : Fin 9), 0), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart12 : twoBandAnnulusGraph.Dart := ⟨((1 : Fin 9), 2), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart25 : twoBandAnnulusGraph.Dart := ⟨((2 : Fin 9), 5), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart54 : twoBandAnnulusGraph.Dart := ⟨((5 : Fin 9), 4), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart41 : twoBandAnnulusGraph.Dart := ⟨((4 : Fin 9), 1), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart20 : twoBandAnnulusGraph.Dart := ⟨((2 : Fin 9), 0), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart03 : twoBandAnnulusGraph.Dart := ⟨((0 : Fin 9), 3), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart35 : twoBandAnnulusGraph.Dart := ⟨((3 : Fin 9), 5), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart52 : twoBandAnnulusGraph.Dart := ⟨((5 : Fin 9), 2), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart34 : twoBandAnnulusGraph.Dart := ⟨((3 : Fin 9), 4), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart47 : twoBandAnnulusGraph.Dart := ⟨((4 : Fin 9), 7), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart76 : twoBandAnnulusGraph.Dart := ⟨((7 : Fin 9), 6), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart63 : twoBandAnnulusGraph.Dart := ⟨((6 : Fin 9), 3), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart45 : twoBandAnnulusGraph.Dart := ⟨((4 : Fin 9), 5), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart58 : twoBandAnnulusGraph.Dart := ⟨((5 : Fin 9), 8), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart87 : twoBandAnnulusGraph.Dart := ⟨((8 : Fin 9), 7), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart74 : twoBandAnnulusGraph.Dart := ⟨((7 : Fin 9), 4), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart53 : twoBandAnnulusGraph.Dart := ⟨((5 : Fin 9), 3), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart36 : twoBandAnnulusGraph.Dart := ⟨((3 : Fin 9), 6), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart68 : twoBandAnnulusGraph.Dart := ⟨((6 : Fin 9), 8), by
  simp [twoBandAnnulusGraph]⟩

def tbaDart85 : twoBandAnnulusGraph.Dart := ⟨((8 : Fin 9), 5), by
  simp [twoBandAnnulusGraph]⟩

macro "tba_dart_cycle" : tactic =>
  `(tactic| simp [SimpleGraph.DartAdj, tbaDart01, tbaDart14, tbaDart43, tbaDart30,
    tbaDart12, tbaDart25, tbaDart54, tbaDart41, tbaDart20, tbaDart03, tbaDart35,
    tbaDart52, tbaDart34, tbaDart47, tbaDart76, tbaDart63, tbaDart45, tbaDart58,
    tbaDart87, tbaDart74, tbaDart53, tbaDart36, tbaDart68, tbaDart85])

def twoBandOuterFace0PureDartCycle
    (hf : (0 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoBandAnnulusEmbedding ⟨(0 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart01, tbaDart14, tbaDart43, tbaDart30]
  hnonempty := by simp
  hclosed := by tba_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary, tbaO01, tbaR1,
        tbaM01, tbaR0, tbaDart01, tbaDart14, tbaDart43, tbaDart30]
  hface_sub := by
    intro e he
    have he' : e = tbaO01 ∨ e = tbaR1 ∨ e = tbaM01 ∨ e = tbaR0 := by
      simpa [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [tbaO01, tbaR1, tbaM01, tbaR0, tbaDart01, tbaDart14, tbaDart43,
        tbaDart30]

def twoBandOuterFace1PureDartCycle
    (hf : (1 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoBandAnnulusEmbedding ⟨(1 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart12, tbaDart25, tbaDart54, tbaDart41]
  hnonempty := by simp
  hclosed := by tba_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary, tbaO12, tbaR2,
        tbaM12, tbaR1, tbaDart12, tbaDart25, tbaDart54, tbaDart41]
  hface_sub := by
    intro e he
    have he' : e = tbaO12 ∨ e = tbaR2 ∨ e = tbaM12 ∨ e = tbaR1 := by
      simpa [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [tbaO12, tbaR2, tbaM12, tbaR1, tbaDart12, tbaDart25, tbaDart54,
        tbaDart41]

def twoBandOuterFace2PureDartCycle
    (hf : (2 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoBandAnnulusEmbedding ⟨(2 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart20, tbaDart03, tbaDart35, tbaDart52]
  hnonempty := by simp
  hclosed := by tba_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary, tbaO20, tbaR0,
        tbaM20, tbaR2, tbaDart20, tbaDart03, tbaDart35, tbaDart52]
  hface_sub := by
    intro e he
    have he' : e = tbaO20 ∨ e = tbaR0 ∨ e = tbaM20 ∨ e = tbaR2 := by
      simpa [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [tbaO20, tbaR0, tbaM20, tbaR2, tbaDart20, tbaDart03, tbaDart35,
        tbaDart52]

def twoBandInnerFace0PureDartCycle
    (hf : (3 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoBandAnnulusEmbedding ⟨(3 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart34, tbaDart47, tbaDart76, tbaDart63]
  hnonempty := by simp
  hclosed := by tba_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary, tbaM01, tbaS1,
        tbaI01, tbaS0, tbaDart34, tbaDart47, tbaDart76, tbaDart63]
  hface_sub := by
    intro e he
    have he' : e = tbaM01 ∨ e = tbaS1 ∨ e = tbaI01 ∨ e = tbaS0 := by
      simpa [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [tbaM01, tbaS1, tbaI01, tbaS0, tbaDart34, tbaDart47, tbaDart76,
        tbaDart63]

def twoBandInnerFace1PureDartCycle
    (hf : (4 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoBandAnnulusEmbedding ⟨(4 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart45, tbaDart58, tbaDart87, tbaDart74]
  hnonempty := by simp
  hclosed := by tba_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary, tbaM12, tbaS2,
        tbaI12, tbaS1, tbaDart45, tbaDart58, tbaDart87, tbaDart74]
  hface_sub := by
    intro e he
    have he' : e = tbaM12 ∨ e = tbaS2 ∨ e = tbaI12 ∨ e = tbaS1 := by
      simpa [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [tbaM12, tbaS2, tbaI12, tbaS1, tbaDart45, tbaDart58, tbaDart87,
        tbaDart74]

def twoBandInnerFace2PureDartCycle
    (hf : (5 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoBandAnnulusEmbedding ⟨(5 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart53, tbaDart36, tbaDart68, tbaDart85]
  hnonempty := by simp
  hclosed := by tba_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary, tbaM20, tbaS0,
        tbaI20, tbaS2, tbaDart53, tbaDart36, tbaDart68, tbaDart85]
  hface_sub := by
    intro e he
    have he' : e = tbaM20 ∨ e = tbaS0 ∨ e = tbaI20 ∨ e = tbaS2 := by
      simpa [twoBandAnnulusEmbedding, twoBandAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [tbaM20, tbaS0, tbaI20, tbaS2, tbaDart53, tbaDart36, tbaDart68,
        tbaDart85]

def twoBandAnnulusPureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry
      twoBandAnnulusEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change TwoBandAnnulusFace at f
    by_cases h0 : f = (0 : TwoBandAnnulusFace)
    · subst f
      exact twoBandOuterFace0PureDartCycle hfmem
    · by_cases h1 : f = (1 : TwoBandAnnulusFace)
      · subst f
        exact twoBandOuterFace1PureDartCycle hfmem
      · by_cases h2 : f = (2 : TwoBandAnnulusFace)
        · subst f
          exact twoBandOuterFace2PureDartCycle hfmem
        · by_cases h3 : f = (3 : TwoBandAnnulusFace)
          · subst f
            exact twoBandInnerFace0PureDartCycle hfmem
          · by_cases h4 : f = (4 : TwoBandAnnulusFace)
            · subst f
              exact twoBandInnerFace1PureDartCycle hfmem
            · have h5 : f = (5 : TwoBandAnnulusFace) := by
                rcases f with ⟨n, hn⟩
                have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
                  omega
                rcases hn_cases with rfl | rfl | rfl | rfl | rfl | rfl
                · exact False.elim (h0 rfl)
                · exact False.elim (h1 rfl)
                · exact False.elim (h2 rfl)
                · exact False.elim (h3 rfl)
                · exact False.elim (h4 rfl)
                · rfl
              subst f
              exact twoBandInnerFace2PureDartCycle hfmem

theorem twoBandAnnulusFace_cases
    (f : AmbientFace twoBandAnnulusEmbedding.faces) :
    f = twoBandOuterFace0 ∨
      f = ⟨(1 : TwoBandAnnulusFace), by simp [twoBandAnnulusEmbedding, twoBandAnnulusFaces]⟩ ∨
      f = ⟨(2 : TwoBandAnnulusFace), by simp [twoBandAnnulusEmbedding, twoBandAnnulusFaces]⟩ ∨
      f = twoBandInnerFace0 ∨
      f = ⟨(4 : TwoBandAnnulusFace), by simp [twoBandAnnulusEmbedding, twoBandAnnulusFaces]⟩ ∨
      f = ⟨(5 : TwoBandAnnulusFace), by simp [twoBandAnnulusEmbedding, twoBandAnnulusFaces]⟩ := by
  rcases f with ⟨⟨n, hn⟩, hfmem⟩
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hn_cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext rfl)

def twoBandAnnulusClosedWalkEmbeddingData :
    PlanarBoundaryClosedWalkEmbeddingData twoBandAnnulusEmbedding :=
  twoBandAnnulusPureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

theorem twoBandAnnulusClosedWalkEmbeddingData_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace twoBandAnnulusEmbedding.faces,
      (twoBandAnnulusClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f := by
  intro f
  rcases twoBandAnnulusFace_cases f with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    refine ⟨[tbaO01], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        decide
  ·
    refine ⟨[tbaO12], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        decide
  ·
    refine ⟨[tbaO20], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        decide
  ·
    refine ⟨[tbaI01], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        decide
  ·
    refine ⟨[tbaI12], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        decide
  ·
    refine ⟨[tbaI20], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        decide

def twoBandOuterFace0DartSuccessor (d : twoBandAnnulusGraph.Dart) :
    twoBandAnnulusGraph.Dart :=
  if d = tbaDart01 then tbaDart14
  else if d = tbaDart14 then tbaDart43
  else if d = tbaDart43 then tbaDart30
  else tbaDart01

def twoBandOuterFace1DartSuccessor (d : twoBandAnnulusGraph.Dart) :
    twoBandAnnulusGraph.Dart :=
  if d = tbaDart12 then tbaDart25
  else if d = tbaDart25 then tbaDart54
  else if d = tbaDart54 then tbaDart41
  else tbaDart12

def twoBandOuterFace2DartSuccessor (d : twoBandAnnulusGraph.Dart) :
    twoBandAnnulusGraph.Dart :=
  if d = tbaDart20 then tbaDart03
  else if d = tbaDart03 then tbaDart35
  else if d = tbaDart35 then tbaDart52
  else tbaDart20

def twoBandInnerFace0DartSuccessor (d : twoBandAnnulusGraph.Dart) :
    twoBandAnnulusGraph.Dart :=
  if d = tbaDart34 then tbaDart47
  else if d = tbaDart47 then tbaDart76
  else if d = tbaDart76 then tbaDart63
  else tbaDart34

def twoBandInnerFace1DartSuccessor (d : twoBandAnnulusGraph.Dart) :
    twoBandAnnulusGraph.Dart :=
  if d = tbaDart45 then tbaDart58
  else if d = tbaDart58 then tbaDart87
  else if d = tbaDart87 then tbaDart74
  else tbaDart45

def twoBandInnerFace2DartSuccessor (d : twoBandAnnulusGraph.Dart) :
    twoBandAnnulusGraph.Dart :=
  if d = tbaDart53 then tbaDart36
  else if d = tbaDart36 then tbaDart68
  else if d = tbaDart68 then tbaDart85
  else tbaDart53

def twoBandOuterFace0DartSuccessorCycle
    (hf : (0 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      twoBandAnnulusEmbedding ⟨(0 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart01, tbaDart14, tbaDart43, tbaDart30]
  hnonempty := by simp
  successor := twoBandOuterFace0DartSuccessor
  hsuccessor_order := by
    simp [twoBandOuterFace0DartSuccessor, tbaDart01, tbaDart14, tbaDart43, tbaDart30]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, twoBandOuterFace0DartSuccessor, tbaDart01, tbaDart14,
        tbaDart43, tbaDart30]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (twoBandOuterFace0PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (twoBandOuterFace0PureDartCycle hf).hface_sub e he

def twoBandOuterFace1DartSuccessorCycle
    (hf : (1 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      twoBandAnnulusEmbedding ⟨(1 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart12, tbaDart25, tbaDart54, tbaDart41]
  hnonempty := by simp
  successor := twoBandOuterFace1DartSuccessor
  hsuccessor_order := by
    simp [twoBandOuterFace1DartSuccessor, tbaDart12, tbaDart25, tbaDart54, tbaDart41]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, twoBandOuterFace1DartSuccessor, tbaDart12, tbaDart25,
        tbaDart54, tbaDart41]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (twoBandOuterFace1PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (twoBandOuterFace1PureDartCycle hf).hface_sub e he

def twoBandOuterFace2DartSuccessorCycle
    (hf : (2 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      twoBandAnnulusEmbedding ⟨(2 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart20, tbaDart03, tbaDart35, tbaDart52]
  hnonempty := by simp
  successor := twoBandOuterFace2DartSuccessor
  hsuccessor_order := by
    simp [twoBandOuterFace2DartSuccessor, tbaDart20, tbaDart03, tbaDart35, tbaDart52]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, twoBandOuterFace2DartSuccessor, tbaDart20, tbaDart03,
        tbaDart35, tbaDart52]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (twoBandOuterFace2PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (twoBandOuterFace2PureDartCycle hf).hface_sub e he

def twoBandInnerFace0DartSuccessorCycle
    (hf : (3 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      twoBandAnnulusEmbedding ⟨(3 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart34, tbaDart47, tbaDart76, tbaDart63]
  hnonempty := by simp
  successor := twoBandInnerFace0DartSuccessor
  hsuccessor_order := by
    simp [twoBandInnerFace0DartSuccessor, tbaDart34, tbaDart47, tbaDart76, tbaDart63]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, twoBandInnerFace0DartSuccessor, tbaDart34, tbaDart47,
        tbaDart76, tbaDart63]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (twoBandInnerFace0PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (twoBandInnerFace0PureDartCycle hf).hface_sub e he

def twoBandInnerFace1DartSuccessorCycle
    (hf : (4 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      twoBandAnnulusEmbedding ⟨(4 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart45, tbaDart58, tbaDart87, tbaDart74]
  hnonempty := by simp
  successor := twoBandInnerFace1DartSuccessor
  hsuccessor_order := by
    simp [twoBandInnerFace1DartSuccessor, tbaDart45, tbaDart58, tbaDart87, tbaDart74]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, twoBandInnerFace1DartSuccessor, tbaDart45, tbaDart58,
        tbaDart87, tbaDart74]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (twoBandInnerFace1PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (twoBandInnerFace1PureDartCycle hf).hface_sub e he

def twoBandInnerFace2DartSuccessorCycle
    (hf : (5 : TwoBandAnnulusFace) ∈ twoBandAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      twoBandAnnulusEmbedding ⟨(5 : TwoBandAnnulusFace), hf⟩ where
  darts := [tbaDart53, tbaDart36, tbaDart68, tbaDart85]
  hnonempty := by simp
  successor := twoBandInnerFace2DartSuccessor
  hsuccessor_order := by
    simp [twoBandInnerFace2DartSuccessor, tbaDart53, tbaDart36, tbaDart68, tbaDart85]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, twoBandInnerFace2DartSuccessor, tbaDart53, tbaDart36,
        tbaDart68, tbaDart85]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (twoBandInnerFace2PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (twoBandInnerFace2PureDartCycle hf).hface_sub e he

def twoBandAnnulusDartSuccessorCycleGeometry :
    PlanarBoundaryDartSuccessorCycleEmbeddingData twoBandAnnulusEmbedding where
  faceBoundaryDartSuccessorCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change TwoBandAnnulusFace at f
    by_cases h0 : f = (0 : TwoBandAnnulusFace)
    · subst f
      exact twoBandOuterFace0DartSuccessorCycle hfmem
    · by_cases h1 : f = (1 : TwoBandAnnulusFace)
      · subst f
        exact twoBandOuterFace1DartSuccessorCycle hfmem
      · by_cases h2 : f = (2 : TwoBandAnnulusFace)
        · subst f
          exact twoBandOuterFace2DartSuccessorCycle hfmem
        · by_cases h3 : f = (3 : TwoBandAnnulusFace)
          · subst f
            exact twoBandInnerFace0DartSuccessorCycle hfmem
          · by_cases h4 : f = (4 : TwoBandAnnulusFace)
            · subst f
              exact twoBandInnerFace1DartSuccessorCycle hfmem
            · have h5 : f = (5 : TwoBandAnnulusFace) := by
                rcases f with ⟨n, hn⟩
                have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
                  omega
                rcases hn_cases with rfl | rfl | rfl | rfl | rfl | rfl
                · exact False.elim (h0 rfl)
                · exact False.elim (h1 rfl)
                · exact False.elim (h2 rfl)
                · exact False.elim (h3 rfl)
                · exact False.elim (h4 rfl)
                · rfl
              subst f
              exact twoBandInnerFace2DartSuccessorCycle hfmem

theorem nonempty_twoBandAnnulusDartSuccessorCycleGeometry :
    Nonempty
      (PlanarBoundaryDartSuccessorCycleEmbeddingData
        twoBandAnnulusEmbedding) :=
  ⟨twoBandAnnulusDartSuccessorCycleGeometry⟩

theorem twoBandAnnulusDartSuccessorCycleGeometry_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace twoBandAnnulusEmbedding.faces,
      (twoBandAnnulusDartSuccessorCycleGeometry.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f := by
  intro f
  rcases twoBandAnnulusFace_cases f with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    refine ⟨[tbaO01], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        decide
  ·
    refine ⟨[tbaO12], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        decide
  ·
    refine ⟨[tbaO20], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        decide
  ·
    refine ⟨[tbaI01], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        decide
  ·
    refine ⟨[tbaI12], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        decide
  ·
    refine ⟨[tbaI20], ?_, ?_⟩
    · decide
    · intro e
      rcases twoBandAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        decide

def twoBandClosedWalkAnnulusBoundarySource :
    PlanarBoundaryClosedWalkAnnulusBoundarySource twoBandAnnulusEmbedding :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields
    twoBandAnnulusBoundaryReachabilityData
    twoBandAnnulusClosedWalkEmbeddingData
    twoBandAnnulusClosedWalkEmbeddingData_selectedBoundaryArcOnFace

def twoBandDartSuccessorClosedWalkAnnulusBoundarySource :
    PlanarBoundaryClosedWalkAnnulusBoundarySource twoBandAnnulusEmbedding :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
    twoBandAnnulusBoundaryReachabilityData
    twoBandAnnulusDartSuccessorCycleGeometry
    twoBandAnnulusDartSuccessorCycleGeometry_selectedBoundaryArcOnFace

noncomputable def twoBandAnnulusBoundaryData :
    PlanarBoundaryAnnulusBoundaryData twoBandAnnulusEmbedding :=
  twoBandClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData

theorem twoBandDartSuccessorClosedWalkAnnulusBoundaryData_eq :
    twoBandDartSuccessorClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData =
      twoBandAnnulusBoundaryData := by
  rfl

theorem twoBandOuterRoot_uniqueReachableRoot_eq :
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
        twoBandAnnulusBoundaryReachabilityData.rootSet
        twoBandAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        twoBandOuterRoot = twoBandOuterRoot := by
  let T := planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding
  let roots := twoBandAnnulusBoundaryReachabilityData.rootSet
  let hroots := twoBandAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
  apply (hroots twoBandOuterRoot).unique
  · exact ⟨uniqueReachableRoot_mem_roots T roots hroots twoBandOuterRoot,
      reachable_uniqueReachableRoot T roots hroots twoBandOuterRoot⟩
  · exact ⟨by
        change twoBandOuterRoot ∈ ({twoBandOuterRoot, twoBandInnerRoot} :
          Finset (PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding))
        simp,
      SimpleGraph.Reachable.refl _⟩

theorem twoBandInnerRoot_uniqueReachableRoot_eq :
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding)
        twoBandAnnulusBoundaryReachabilityData.rootSet
        twoBandAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        twoBandInnerRoot = twoBandInnerRoot := by
  let T := planarBoundarySupportEndpointAdjGraph twoBandAnnulusEmbedding
  let roots := twoBandAnnulusBoundaryReachabilityData.rootSet
  let hroots := twoBandAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
  apply (hroots twoBandInnerRoot).unique
  · exact ⟨uniqueReachableRoot_mem_roots T roots hroots twoBandInnerRoot,
      reachable_uniqueReachableRoot T roots hroots twoBandInnerRoot⟩
  · exact ⟨by
        change twoBandInnerRoot ∈ ({twoBandOuterRoot, twoBandInnerRoot} :
          Finset (PlanarBoundaryEdgeVertex twoBandAnnulusEmbedding))
        simp,
      SimpleGraph.Reachable.refl _⟩

theorem tbaO01_mem_twoBandAnnulusOuterAmbientBoundary :
    tbaO01 ∈ twoBandAnnulusBoundaryData.outerAmbientBoundary := by
  simpa [twoBandAnnulusBoundaryData, twoBandOuterRoot] using
    PlanarBoundaryAnnulusBoundaryReachabilityData.mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
      (data := twoBandAnnulusBoundaryReachabilityData)
      (e := twoBandOuterRoot) twoBandOuterRoot_uniqueReachableRoot_eq

theorem tbaI01_mem_twoBandAnnulusInnerAmbientBoundary :
    tbaI01 ∈ twoBandAnnulusBoundaryData.innerAmbientBoundary := by
  simpa [twoBandAnnulusBoundaryData, twoBandInnerRoot] using
    PlanarBoundaryAnnulusBoundaryReachabilityData.mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
      (data := twoBandAnnulusBoundaryReachabilityData)
      (e := twoBandInnerRoot) twoBandInnerRoot_uniqueReachableRoot_eq

theorem twoBandOuterFace0_mem_outerBoundaryFaces :
    twoBandOuterFace0 ∈ twoBandAnnulusBoundaryData.outerBoundaryFaces := by
  exact
    (twoBandAnnulusBoundaryData.mem_outerBoundaryFaces_iff).2
      ⟨tbaO01, by decide, tbaO01_mem_twoBandAnnulusOuterAmbientBoundary⟩

theorem twoBandInnerFace0_mem_innerBoundaryFaces :
    twoBandInnerFace0 ∈ twoBandAnnulusBoundaryData.innerBoundaryFaces := by
  exact
    (twoBandAnnulusBoundaryData.mem_innerBoundaryFaces_iff).2
      ⟨tbaI01, by decide, tbaI01_mem_twoBandAnnulusInnerAmbientBoundary⟩

theorem twoBandOuterFace0_mem_dartSuccessorOuterBoundaryFaces :
    twoBandOuterFace0 ∈
      twoBandDartSuccessorClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces := by
  simpa [twoBandDartSuccessorClosedWalkAnnulusBoundaryData_eq] using
    twoBandOuterFace0_mem_outerBoundaryFaces

theorem twoBandInnerFace0_mem_dartSuccessorInnerBoundaryFaces :
    twoBandInnerFace0 ∈
      twoBandDartSuccessorClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  simpa [twoBandDartSuccessorClosedWalkAnnulusBoundaryData_eq] using
    twoBandInnerFace0_mem_innerBoundaryFaces

theorem twoBandAnnulus_interiorDual_adj_outer0_inner0 :
    (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary
      twoBandAnnulusEmbedding.faces).Adj twoBandOuterFace0 twoBandInnerFace0 := by
  refine (interiorDualGraph_adj_iff twoBandAnnulusEmbedding.faceBoundary
    twoBandAnnulusEmbedding.faces).2 ?_
  refine ⟨?_, tbaM01, tbaM01_mem_interiorEdgeSupport, ?_, ?_⟩
  · intro h
    have hnat : (0 : Nat) = 3 := by
      simpa [twoBandOuterFace0, twoBandInnerFace0] using congrArg Fin.val h
    omega
  · decide
  · decide

/-- The source-extracted boundary-face roots for the two-band annulus are exactly all six strip
faces: every face touches one of the six selected ambient boundary edges. -/
theorem twoBandAnnulusBoundaryFaceRoots_eq_univ :
    twoBandClosedWalkAnnulusBoundarySource.boundaryFaceRoots = Finset.univ := by
  ext f
  constructor
  · intro _hf
    simp
  · intro _hf
    change f ∈ twoBandAnnulusBoundaryData.outerBoundaryFaces ∪
      twoBandAnnulusBoundaryData.innerBoundaryFaces
    apply (twoBandAnnulusBoundaryData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_iff).2
    rcases twoBandAnnulusFace_cases f with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨tbaO01, by decide, tbaO01_mem_selectedBoundarySupport⟩
    · exact ⟨tbaO12, by decide, tbaO12_mem_selectedBoundarySupport⟩
    · exact ⟨tbaO20, by decide, tbaO20_mem_selectedBoundarySupport⟩
    · exact ⟨tbaI01, by decide, tbaI01_mem_selectedBoundarySupport⟩
    · exact ⟨tbaI12, by decide, tbaI12_mem_selectedBoundarySupport⟩
    · exact ⟨tbaI20, by decide, tbaI20_mem_selectedBoundarySupport⟩

/-- On the concrete two-band annulus, the fixed source boundary-face roots do cover the interior
dual graph: every face is itself a root.  Thus the source-side constructor fails here only at the
separation premise, not at coverage. -/
theorem rootSetCovers_twoBandAnnulusBoundaryFaceRoots :
    RootSetCovers
      (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces)
      twoBandClosedWalkAnnulusBoundarySource.boundaryFaceRoots := by
  intro f
  refine ⟨f, ?_, SimpleGraph.Reachable.refl f⟩
  rw [twoBandAnnulusBoundaryFaceRoots_eq_univ]
  simp

/-- The source-extracted boundary-face roots for the two-band annulus are not separated in the
interior dual: the outer face `0` and inner face `3` are distinct roots joined by the shared
middle edge `tbaM01`. -/
theorem not_rootSetSeparated_twoBandAnnulusBoundaryFaceRoots :
    ¬ RootSetSeparated
      (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces)
      twoBandClosedWalkAnnulusBoundarySource.boundaryFaceRoots := by
  intro hsep
  have hEq : twoBandOuterFace0 = twoBandInnerFace0 :=
    hsep
      (by rw [twoBandAnnulusBoundaryFaceRoots_eq_univ]; simp)
      (by rw [twoBandAnnulusBoundaryFaceRoots_eq_univ]; simp)
      twoBandAnnulus_interiorDual_adj_outer0_inner0.reachable
  have hnat : (0 : Nat) = 3 := by
    simpa [twoBandOuterFace0, twoBandInnerFace0] using
      congrArg (fun f : AmbientFace twoBandAnnulusEmbedding.faces => f.1.val) hEq
  omega

/-- The concrete fixed-root source-side premise has the expected shape on this annulus: coverage
holds, while root separation fails. -/
theorem twoBandAnnulusBoundaryFaceRoots_cover_not_separated :
    RootSetCovers
        (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces)
        twoBandClosedWalkAnnulusBoundarySource.boundaryFaceRoots ∧
      ¬ RootSetSeparated
        (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces)
        twoBandClosedWalkAnnulusBoundarySource.boundaryFaceRoots :=
  ⟨rootSetCovers_twoBandAnnulusBoundaryFaceRoots,
    not_rootSetSeparated_twoBandAnnulusBoundaryFaceRoots⟩

theorem twoBandDartSuccessorBoundaryFaceRoots_eq_univ :
    twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots = Finset.univ := by
  rw [PlanarBoundaryClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
    twoBandDartSuccessorClosedWalkAnnulusBoundaryData_eq]
  simpa [PlanarBoundaryClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
    twoBandAnnulusBoundaryData] using twoBandAnnulusBoundaryFaceRoots_eq_univ

theorem rootSetCovers_twoBandDartSuccessorBoundaryFaceRoots :
    RootSetCovers
      (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces)
      twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots := by
  intro f
  refine ⟨f, ?_, SimpleGraph.Reachable.refl f⟩
  rw [twoBandDartSuccessorBoundaryFaceRoots_eq_univ]
  simp

theorem twoBandDartSuccessorBoundaryFaceRoots_cover_not_separated :
    RootSetCovers
        (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces)
        twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots ∧
      ¬ RootSetSeparated
        (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces)
        twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots := by
  refine ⟨rootSetCovers_twoBandDartSuccessorBoundaryFaceRoots, ?_⟩
  intro hsep
  have hEq : twoBandOuterFace0 = twoBandInnerFace0 :=
    hsep
      (by rw [twoBandDartSuccessorBoundaryFaceRoots_eq_univ]; simp)
      (by rw [twoBandDartSuccessorBoundaryFaceRoots_eq_univ]; simp)
      twoBandAnnulus_interiorDual_adj_outer0_inner0.reachable
  have hnat : (0 : Nat) = 3 := by
    simpa [twoBandOuterFace0, twoBandInnerFace0] using
      congrArg (fun f : AmbientFace twoBandAnnulusEmbedding.faces => f.1.val) hEq
  omega

/-- In the concrete two-band annulus, every ambient face touches the selected boundary support.
Consequently, any set of faces whose boundaries are disjoint from the selected boundary support
is empty. -/
theorem twoBandAnnulus_peelFaces_eq_empty_of_boundaryFree
    {peelFaces : Finset (AmbientFace twoBandAnnulusEmbedding.faces)}
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (twoBandAnnulusEmbedding.faceBoundary f.1)
        (selectedBoundarySupport twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces)) :
    peelFaces = ∅ := by
  ext f
  constructor
  · intro hf
    exfalso
    have hfRoot : f ∈ twoBandClosedWalkAnnulusBoundarySource.boundaryFaceRoots := by
      rw [twoBandAnnulusBoundaryFaceRoots_eq_univ]
      simp
    have hfBoundary :
        f ∈ twoBandAnnulusBoundaryData.outerBoundaryFaces ∪
          twoBandAnnulusBoundaryData.innerBoundaryFaces := by
      simpa [twoBandAnnulusBoundaryData,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.boundaryFaceRoots] using hfRoot
    rcases (twoBandAnnulusBoundaryData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_iff).1
        hfBoundary with ⟨e, hef, heSelected⟩
    exact (Finset.disjoint_left.mp (hpeelInterior f hf)) hef heSelected
  · intro hf
    simp at hf

/-- The concrete two-band annulus cannot have its interior-edge support covered by any image of
boundary-free peel faces.  The middle edge `tbaM01` is an interior edge, while the preceding lemma
forces every boundary-free peel-face set to be empty. -/
theorem not_interiorEdgeSupport_subset_boundaryFreePeelImage_twoBandAnnulus
    {peelFaces : Finset (AmbientFace twoBandAnnulusEmbedding.faces)}
    (witnessEdge :
      AmbientFace twoBandAnnulusEmbedding.faces → twoBandAnnulusGraph.edgeSet)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (twoBandAnnulusEmbedding.faceBoundary f.1)
        (selectedBoundarySupport twoBandAnnulusEmbedding.faceBoundary
          twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces)) :
    ¬ interiorEdgeSupport twoBandAnnulusEmbedding.faceBoundary
        twoBandAnnulusEmbedding.faces ⊆ peelFaces.image witnessEdge := by
  intro hcover
  have hEmpty := twoBandAnnulus_peelFaces_eq_empty_of_boundaryFree hpeelInterior
  have hmem : tbaM01 ∈ peelFaces.image witnessEdge := hcover tbaM01_mem_interiorEdgeSupport
  simp [hEmpty] at hmem

/-- The middle edge `tbaM01` is a forcing interior edge for the concrete two-band annulus:
every incident face already contains selected boundary support. -/
def twoBandAnnulusForcingInteriorEdgeWitness :
    ForcingInteriorEdgeWitness twoBandAnnulusEmbedding where
  edge := tbaM01
  heInterior := tbaM01_mem_interiorEdgeSupport
  hforcing := by
    intro f _hf
    have hfRoot : f ∈ twoBandClosedWalkAnnulusBoundarySource.boundaryFaceRoots := by
      rw [twoBandAnnulusBoundaryFaceRoots_eq_univ]
      simp
    have hfBoundary :
        f ∈ twoBandAnnulusBoundaryData.outerBoundaryFaces ∪
          twoBandAnnulusBoundaryData.innerBoundaryFaces := by
      simpa [twoBandAnnulusBoundaryData,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.boundaryFaceRoots] using hfRoot
    exact
      (twoBandAnnulusBoundaryData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_iff).1
        hfBoundary

theorem nonempty_forcingInteriorEdgeWitness_twoBandAnnulus :
    Nonempty (ForcingInteriorEdgeWitness twoBandAnnulusEmbedding) :=
  ⟨twoBandAnnulusForcingInteriorEdgeWitness⟩

/-- The concrete two-band annulus fails the positive local no-forcing condition. -/
theorem not_everyInteriorEdgeHasBoundaryFreeIncidentFace_twoBandAnnulus :
    ¬ EveryInteriorEdgeHasBoundaryFreeIncidentFace twoBandAnnulusEmbedding := by
  intro hfree
  exact
    not_nonempty_forcingInteriorEdgeWitness_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
      hfree nonempty_forcingInteriorEdgeWitness_twoBandAnnulus

/-- Consequently, the two-band annulus has no boundary-free incident-face selector. -/
theorem not_nonempty_boundaryFreeIncidentFaceSelector_twoBandAnnulus :
    ¬ Nonempty (BoundaryFreeIncidentFaceSelector twoBandAnnulusEmbedding) := by
  exact
    (not_nonempty_boundaryFreeIncidentFaceSelector_iff_nonempty_forcingInteriorEdgeWitness).2
      nonempty_forcingInteriorEdgeWitness_twoBandAnnulus

/-- The same forcing edge gives an independent proof that the interior-dual boundary-root
adjacency-distance package is impossible on the two-band annulus. -/
theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_twoBandAnnulus_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData
      (emb := twoBandAnnulusEmbedding)
      twoBandAnnulusForcingInteriorEdgeWitness

/-- The forcing edge also rules out the annulus-root adjacency-distance package on this
embedding, before any theorem-4.9 synthesis layer is reached. -/
theorem not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_twoBandAnnulus_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData twoBandAnnulusEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
      (emb := twoBandAnnulusEmbedding)
      twoBandAnnulusForcingInteriorEdgeWitness

/-- The same forcing edge also rules out the generic source-fixed canonical-parent payload on
this embedding. -/
theorem not_nonempty_interiorDualBoundaryRootParentPeelData_twoBandAnnulus_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (InteriorDualBoundaryRootParentPeelData
      twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootParentPeelData
      (emb := twoBandAnnulusEmbedding)
      twoBandAnnulusForcingInteriorEdgeWitness

/-- Consequently the two-sided annulus-root parent package is impossible on the same honest
two-band source embedding. -/
theorem not_nonempty_planarBoundaryAnnulusRootParentPeelData_twoBandAnnulus_via_forcingInteriorEdgeWitness :
    ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData twoBandAnnulusEmbedding) := by
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData
      (emb := twoBandAnnulusEmbedding)
      twoBandAnnulusForcingInteriorEdgeWitness

/-- The same forcing edge also blocks the live successor-cycle raw canonical-parent shared-edge
cover shell on the concrete two-band annulus. Since that shell would already yield a
boundary-free selector on the same embedding, it cannot coexist with the forcing interior edge
at `tbaM01`. -/
theorem
    not_exists_twoBandAnnulus_boundaryFaceRootsCanonicalParentSharedEdgeCover_via_forcingInteriorEdgeWitness :
    ¬ (∃ peelFaces : Finset (AmbientFace twoBandAnnulusEmbedding.faces),
      ∃ hunique :
          PairwiseUniqueSharedInteriorEdges
            twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces,
      ∃ hcoverRoots : RootSetCovers
          (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary
            twoBandAnnulusEmbedding.faces)
          twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated
          (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary
            twoBandAnnulusEmbedding.faces)
          twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (twoBandAnnulusEmbedding.faceBoundary f.1)
            (selectedBoundarySupport twoBandAnnulusEmbedding.faceBoundary
              twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces)) ∧
        interiorEdgeSupport twoBandAnnulusEmbedding.faceBoundary
            twoBandAnnulusEmbedding.faces ⊆
          peelFaces.image
            (rootedSharedInteriorEdgeOfPairwiseUnique
              twoBandAnnulusEmbedding.faceBoundary
              twoBandAnnulusEmbedding.faces hunique
              (interiorDualSpanningForestRoot
                twoBandAnnulusEmbedding.faceBoundary
                twoBandAnnulusEmbedding.faces
                twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                hcoverRoots hsepRoots)
              twoBandDartSuccessorClosedWalkAnnulusBoundarySource.fallbackEdge)) := by
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_forcingInteriorEdgeWitness
      twoBandAnnulusBoundaryReachabilityData
      twoBandAnnulusDartSuccessorCycleGeometry
      twoBandAnnulusDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      twoBandAnnulusForcingInteriorEdgeWitness

/-- The same concrete successor-cycle parent-cover shell also cannot repair itself by the older
endpoint-support carrier route. Even if one only asks for raw endpoint-support separation and a
nonempty interior-edge endpoint carrier, the abstract parent-cover obstruction already rules out
that package on the two-band annulus. -/
theorem
    not_exists_twoBandAnnulus_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport :
    ¬ (∃ peelFaces : Finset (AmbientFace twoBandAnnulusEmbedding.faces),
      ∃ hunique :
          PairwiseUniqueSharedInteriorEdges
            twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces,
      ∃ hcoverRoots : RootSetCovers
          (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary
            twoBandAnnulusEmbedding.faces)
          twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated
          (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary
            twoBandAnnulusEmbedding.faces)
          twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (twoBandAnnulusEmbedding.faceBoundary f.1)
            (selectedBoundarySupport twoBandAnnulusEmbedding.faceBoundary
              twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces)) ∧
        interiorEdgeSupport twoBandAnnulusEmbedding.faceBoundary
            twoBandAnnulusEmbedding.faces ⊆
          peelFaces.image
            (rootedSharedInteriorEdgeOfPairwiseUnique
              twoBandAnnulusEmbedding.faceBoundary
              twoBandAnnulusEmbedding.faces hunique
              (interiorDualSpanningForestRoot
                twoBandAnnulusEmbedding.faceBoundary
                twoBandAnnulusEmbedding.faces
                twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                hcoverRoots hsepRoots)
              twoBandDartSuccessorClosedWalkAnnulusBoundarySource.fallbackEdge) ∧
        Disjoint (interiorEdgeEndpointSupport twoBandAnnulusEmbedding)
          (edgeEndpointSupport
            (selectedBoundarySupport twoBandAnnulusEmbedding.faceBoundary
              twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces)) ∧
        (interiorEdgeEndpointSupport twoBandAnnulusEmbedding).Nonempty) := by
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
    hEndpointDisjoint, hRawCarrier⟩
  exact
    not_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      twoBandAnnulusBoundaryReachabilityData
      twoBandAnnulusDartSuccessorCycleGeometry
      twoBandAnnulusDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      ⟨hEndpointDisjoint, hRawCarrier⟩

/-- Concrete source-side instance of the IDBRAD obstruction: the two-band annulus has an honest
closed-walk source, but the extracted outer and inner boundary-face layers are adjacent in the
interior dual, so the generic boundary-root adjacency-distance peel package cannot exist on this
embedding. -/
theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_twoBandAnnulus_via_source_reachability :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faceBoundary) := by
  exact
    twoBandClosedWalkAnnulusBoundarySource
      |>.not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_reachable_outerBoundaryFace_innerBoundaryFace
        twoBandOuterFace0_mem_outerBoundaryFaces
        twoBandInnerFace0_mem_innerBoundaryFaces
        twoBandAnnulus_interiorDual_adj_outer0_inner0.reachable

/-- The same two-band annulus also instantiates the live successor-cycle-shell source boundary-face
root separation obstruction. The derived successor-cycle source still extracts the same outer and
inner boundary-face layers, and those layers are already joined by the shared middle edge
`tbaM01` in the interior dual. -/
theorem not_rootSetSeparated_twoBandAnnulusBoundaryFaceRoots_via_dartSuccessor_source_reachability :
    ¬ RootSetSeparated
      (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces)
      twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots := by
  exact
    not_rootSetSeparated_boundaryFaceRoots_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_reachable_outerBoundaryFace_innerBoundaryFace
      twoBandAnnulusBoundaryReachabilityData
      twoBandAnnulusDartSuccessorCycleGeometry
      twoBandAnnulusDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      twoBandOuterFace0_mem_dartSuccessorOuterBoundaryFaces
      twoBandInnerFace0_mem_dartSuccessorInnerBoundaryFaces
      twoBandAnnulus_interiorDual_adj_outer0_inner0.reachable

/-- The same two-band annulus therefore also refutes generic IDBRAD data directly on the live
successor-cycle shell, not just after lowering to the explicit closed-walk source package. -/
theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_twoBandAnnulus_via_dartSuccessor_source_reachability :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
      twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faceBoundary) := by
  exact
    not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_reachable_outerBoundaryFace_innerBoundaryFace
      twoBandAnnulusBoundaryReachabilityData
      twoBandAnnulusDartSuccessorCycleGeometry
      twoBandAnnulusDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      twoBandOuterFace0_mem_dartSuccessorOuterBoundaryFaces
      twoBandInnerFace0_mem_dartSuccessorInnerBoundaryFaces
      twoBandAnnulus_interiorDual_adj_outer0_inner0.reachable

/-- The same concrete successor-cycle shell cannot satisfy the source-fixed rooted shared-edge
face-membership burden either. Since the shell still extracts an outer boundary face adjacent to
an inner boundary face in the interior dual, no choice of boundary-free peeled faces, rooted
shared-edge cover, and strict child-membership witnesses can exist on this benchmark. -/
theorem
    not_exists_twoBandAnnulus_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_via_dartSuccessor_source_reachability :
    ¬ (∃ peelFaces : Finset (AmbientFace twoBandAnnulusEmbedding.faces),
      ∃ hunique :
          PairwiseUniqueSharedInteriorEdges
            twoBandAnnulusEmbedding.faceBoundary twoBandAnnulusEmbedding.faces,
      ∃ hcoverRoots : RootSetCovers
          (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary
            twoBandAnnulusEmbedding.faces)
          twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated
          (interiorDualGraph twoBandAnnulusEmbedding.faceBoundary
            twoBandAnnulusEmbedding.faces)
          twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (twoBandAnnulusEmbedding.faceBoundary f.1)
            (selectedBoundarySupport twoBandAnnulusEmbedding.faceBoundary
              twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces)) ∧
        interiorEdgeSupport twoBandAnnulusEmbedding.faceBoundary
            twoBandAnnulusEmbedding.faces ⊆
          peelFaces.image
            (rootedSharedInteriorEdgeOfPairwiseUnique
              twoBandAnnulusEmbedding.faceBoundary
              twoBandAnnulusEmbedding.faces hunique
              (interiorDualSpanningForestRoot
                twoBandAnnulusEmbedding.faceBoundary
                twoBandAnnulusEmbedding.faces
                twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                hcoverRoots hsepRoots)
              twoBandDartSuccessorClosedWalkAnnulusBoundarySource.fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (twoBandAnnulusEmbedding.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique
              twoBandAnnulusEmbedding.faceBoundary
              twoBandAnnulusEmbedding.faces hunique
              (interiorDualSpanningForestRoot
                twoBandAnnulusEmbedding.faceBoundary
                twoBandAnnulusEmbedding.faces
                twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                hcoverRoots hsepRoots)
              twoBandDartSuccessorClosedWalkAnnulusBoundarySource.fallbackEdge f),
          e ∈ selectedBoundarySupport twoBandAnnulusEmbedding.faceBoundary
                twoBandAnnulusEmbedding.faces twoBandAnnulusEmbedding.faces ∨
            ∃ g ∈ peelFaces,
              (interiorDualSpanningForest
                twoBandAnnulusEmbedding.faceBoundary
                twoBandAnnulusEmbedding.faces).Adj f g ∧
              e ∈ twoBandAnnulusEmbedding.faceBoundary g.1 ∧
              (interiorDualSpanningForest
                  twoBandAnnulusEmbedding.faceBoundary
                  twoBandAnnulusEmbedding.faces).dist
                  f
                  (interiorDualSpanningForestRoot
                    twoBandAnnulusEmbedding.faceBoundary
                    twoBandAnnulusEmbedding.faces
                    twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                    hcoverRoots hsepRoots f) <
                (interiorDualSpanningForest
                    twoBandAnnulusEmbedding.faceBoundary
                    twoBandAnnulusEmbedding.faces).dist
                    g
                    (interiorDualSpanningForestRoot
                      twoBandAnnulusEmbedding.faceBoundary
                      twoBandAnnulusEmbedding.faces
                      twoBandDartSuccessorClosedWalkAnnulusBoundarySource.boundaryFaceRoots
                      hcoverRoots hsepRoots g))) := by
  rintro ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩
  exact
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover_and_reachable_outerBoundaryFace_innerBoundaryFace
      twoBandAnnulusBoundaryReachabilityData
      twoBandAnnulusDartSuccessorCycleGeometry
      twoBandAnnulusDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren
      twoBandOuterFace0_mem_dartSuccessorOuterBoundaryFaces
      twoBandInnerFace0_mem_dartSuccessorInnerBoundaryFaces
      twoBandAnnulus_interiorDual_adj_outer0_inner0.reachable

end Theorem49PlanarBoundaryAnnulusRootInteriorDualObstructionRegression

end Mettapedia.GraphTheory.FourColor
