import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometry
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusWitness
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryDegenerateCertificate
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

/-- A concrete honest annulus-source model whose outer component consists of two facial cycles
sharing the consecutive interior edges `sip01` and `sip12`, while a disjoint triangle supplies
the second boundary component. This is designed so the source side is completely honest, but the
canonical one-collar decomposition extracted from that source still cannot support witness
ownership. -/
def sharedInteriorPairAnnulusGraph : SimpleGraph (Fin 8) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 3), s(3, 0), s(2, 4), s(4, 0),
        s(5, 6), s(6, 7), s(7, 5)} : Set (Sym2 (Fin 8)))

def sip01 : sharedInteriorPairAnnulusGraph.edgeSet := ⟨s(0, 1), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sip12 : sharedInteriorPairAnnulusGraph.edgeSet := ⟨s(1, 2), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sip23 : sharedInteriorPairAnnulusGraph.edgeSet := ⟨s(2, 3), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sip30 : sharedInteriorPairAnnulusGraph.edgeSet := ⟨s(3, 0), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sip24 : sharedInteriorPairAnnulusGraph.edgeSet := ⟨s(2, 4), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sip40 : sharedInteriorPairAnnulusGraph.edgeSet := ⟨s(4, 0), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sip56 : sharedInteriorPairAnnulusGraph.edgeSet := ⟨s(5, 6), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sip67 : sharedInteriorPairAnnulusGraph.edgeSet := ⟨s(6, 7), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sip75 : sharedInteriorPairAnnulusGraph.edgeSet := ⟨s(7, 5), by
  simp [sharedInteriorPairAnnulusGraph]⟩

theorem sip01_ne_sip12 : sip01 ≠ sip12 := by
  intro h
  have := congrArg Subtype.val h
  simp [sip01, sip12] at this

theorem sip23_ne_sip30 : sip23 ≠ sip30 := by
  intro h
  have := congrArg Subtype.val h
  simp [sip23, sip30] at this

theorem sip24_ne_sip40 : sip24 ≠ sip40 := by
  intro h
  have := congrArg Subtype.val h
  simp [sip24, sip40] at this

theorem sip56_ne_sip67 : sip56 ≠ sip67 := by
  intro h
  have := congrArg Subtype.val h
  simp [sip56, sip67] at this

theorem sip56_ne_sip75 : sip56 ≠ sip75 := by
  intro h
  have := congrArg Subtype.val h
  simp [sip56, sip75] at this

theorem sip67_ne_sip75 : sip67 ≠ sip75 := by
  intro h
  have := congrArg Subtype.val h
  simp [sip67, sip75] at this

theorem sharedInteriorPairAnnulus_edge_eq
    (e : sharedInteriorPairAnnulusGraph.edgeSet) :
    e = sip01 ∨ e = sip12 ∨ e = sip23 ∨ e = sip30 ∨ e = sip24 ∨
      e = sip40 ∨ e = sip56 ∨ e = sip67 ∨ e = sip75 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 3) ∨ e.1 = s(3, 0) ∨
          e.1 = s(2, 4) ∨ e.1 = s(4, 0) ∨ e.1 = s(5, 6) ∨ e.1 = s(6, 7) ∨
          e.1 = s(7, 5)) ∧
        ¬ e.1.IsDiag := by
    simpa [sharedInteriorPairAnnulusGraph] using e.2
  rcases h.1 with h01 | h12 | h23 | h30 | h24 | h40 | h56 | h67 | h75
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr <| Or.inl (Subtype.ext h12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h23)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h30)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h24)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h40)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h56)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext h67)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr (Subtype.ext h75)

def sharedInteriorPairEdgeColor (e : sharedInteriorPairAnnulusGraph.edgeSet) : Color :=
  if e = sip01 ∨ e = sip24 ∨ e = sip56 then red
  else if e = sip12 ∨ e = sip30 ∨ e = sip67 then blue
  else purple

@[simp] theorem sharedInteriorPairEdgeColor_sip01 :
    sharedInteriorPairEdgeColor sip01 = red := by
  simp [sharedInteriorPairEdgeColor]

@[simp] theorem sharedInteriorPairEdgeColor_sip12 :
    sharedInteriorPairEdgeColor sip12 = blue := by
  simp [sharedInteriorPairEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip12, sip24,
    sip30, sip56, sip67]

@[simp] theorem sharedInteriorPairEdgeColor_sip23 :
    sharedInteriorPairEdgeColor sip23 = purple := by
  simp [sharedInteriorPairEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip12, sip23,
    sip24, sip30, sip56, sip67]

@[simp] theorem sharedInteriorPairEdgeColor_sip30 :
    sharedInteriorPairEdgeColor sip30 = blue := by
  simp [sharedInteriorPairEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip12, sip24,
    sip30, sip56, sip67]

@[simp] theorem sharedInteriorPairEdgeColor_sip24 :
    sharedInteriorPairEdgeColor sip24 = red := by
  simp [sharedInteriorPairEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip24]

@[simp] theorem sharedInteriorPairEdgeColor_sip40 :
    sharedInteriorPairEdgeColor sip40 = purple := by
  simp [sharedInteriorPairEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip12, sip24,
    sip30, sip40, sip56, sip67]

@[simp] theorem sharedInteriorPairEdgeColor_sip56 :
    sharedInteriorPairEdgeColor sip56 = red := by
  simp [sharedInteriorPairEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip24, sip56]

@[simp] theorem sharedInteriorPairEdgeColor_sip67 :
    sharedInteriorPairEdgeColor sip67 = blue := by
  simp [sharedInteriorPairEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip12, sip24,
    sip30, sip56, sip67]

@[simp] theorem sharedInteriorPairEdgeColor_sip75 :
    sharedInteriorPairEdgeColor sip75 = purple := by
  simp [sharedInteriorPairEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip12, sip24,
    sip30, sip56, sip67, sip75]

theorem sharedInteriorPair_edge_mem_zero
    {e : sharedInteriorPairAnnulusGraph.edgeSet} (h : (0 : Fin 8) ∈ (e : Sym2 (Fin 8))) :
    e = sip01 ∨ e = sip30 ∨ e = sip40 := by
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairAnnulusGraph, sip01, sip12, sip23, sip30, sip24, sip40,
      sip56, sip67, sip75] at h ⊢

theorem sharedInteriorPair_edge_mem_one
    {e : sharedInteriorPairAnnulusGraph.edgeSet} (h : (1 : Fin 8) ∈ (e : Sym2 (Fin 8))) :
    e = sip01 ∨ e = sip12 := by
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairAnnulusGraph, sip01, sip12, sip23, sip30, sip24, sip40,
      sip56, sip67, sip75] at h ⊢

theorem sharedInteriorPair_edge_mem_two
    {e : sharedInteriorPairAnnulusGraph.edgeSet} (h : (2 : Fin 8) ∈ (e : Sym2 (Fin 8))) :
    e = sip12 ∨ e = sip23 ∨ e = sip24 := by
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairAnnulusGraph, sip01, sip12, sip23, sip30, sip24, sip40,
      sip56, sip67, sip75] at h ⊢

theorem sharedInteriorPair_edge_mem_three
    {e : sharedInteriorPairAnnulusGraph.edgeSet} (h : (3 : Fin 8) ∈ (e : Sym2 (Fin 8))) :
    e = sip23 ∨ e = sip30 := by
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairAnnulusGraph, sip01, sip12, sip23, sip30, sip24, sip40,
      sip56, sip67, sip75] at h ⊢

theorem sharedInteriorPair_edge_mem_four
    {e : sharedInteriorPairAnnulusGraph.edgeSet} (h : (4 : Fin 8) ∈ (e : Sym2 (Fin 8))) :
    e = sip24 ∨ e = sip40 := by
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairAnnulusGraph, sip01, sip12, sip23, sip30, sip24, sip40,
      sip56, sip67, sip75] at h ⊢

theorem sharedInteriorPair_edge_mem_five
    {e : sharedInteriorPairAnnulusGraph.edgeSet} (h : (5 : Fin 8) ∈ (e : Sym2 (Fin 8))) :
    e = sip56 ∨ e = sip75 := by
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairAnnulusGraph, sip01, sip12, sip23, sip30, sip24, sip40,
      sip56, sip67, sip75] at h ⊢

theorem sharedInteriorPair_edge_mem_six
    {e : sharedInteriorPairAnnulusGraph.edgeSet} (h : (6 : Fin 8) ∈ (e : Sym2 (Fin 8))) :
    e = sip56 ∨ e = sip67 := by
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairAnnulusGraph, sip01, sip12, sip23, sip30, sip24, sip40,
      sip56, sip67, sip75] at h ⊢

theorem sharedInteriorPair_edge_mem_seven
    {e : sharedInteriorPairAnnulusGraph.edgeSet} (h : (7 : Fin 8) ∈ (e : Sym2 (Fin 8))) :
    e = sip67 ∨ e = sip75 := by
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairAnnulusGraph, sip01, sip12, sip23, sip30, sip24, sip40,
      sip56, sip67, sip75] at h ⊢

def sharedInteriorPairTaitEdgeColoring :
    sharedInteriorPairAnnulusGraph.EdgeColoring Color :=
  Coloring.mk sharedInteriorPairEdgeColor (by
    intro e f hadj hcolor
    rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
    rcases hadj with ⟨hne, v, he, hf⟩
    fin_cases v
    · rcases sharedInteriorPair_edge_mem_zero he with rfl | rfl | rfl <;>
        rcases sharedInteriorPair_edge_mem_zero hf with rfl | rfl | rfl <;>
        simp [red, blue, purple] at hne hcolor
    · rcases sharedInteriorPair_edge_mem_one he with rfl | rfl <;>
        rcases sharedInteriorPair_edge_mem_one hf with rfl | rfl <;>
        simp [red, blue] at hne hcolor
    · rcases sharedInteriorPair_edge_mem_two he with rfl | rfl | rfl <;>
        rcases sharedInteriorPair_edge_mem_two hf with rfl | rfl | rfl <;>
        simp [red, blue, purple] at hne hcolor
    · rcases sharedInteriorPair_edge_mem_three he with rfl | rfl <;>
        rcases sharedInteriorPair_edge_mem_three hf with rfl | rfl <;>
        simp [blue, purple] at hne hcolor
    · rcases sharedInteriorPair_edge_mem_four he with rfl | rfl <;>
        rcases sharedInteriorPair_edge_mem_four hf with rfl | rfl <;>
        simp [red, purple] at hne hcolor
    · rcases sharedInteriorPair_edge_mem_five he with rfl | rfl <;>
        rcases sharedInteriorPair_edge_mem_five hf with rfl | rfl <;>
        simp [red, purple] at hne hcolor
    · rcases sharedInteriorPair_edge_mem_six he with rfl | rfl <;>
        rcases sharedInteriorPair_edge_mem_six hf with rfl | rfl <;>
        simp [red, blue] at hne hcolor
    · rcases sharedInteriorPair_edge_mem_seven he with rfl | rfl <;>
        rcases sharedInteriorPair_edge_mem_seven hf with rfl | rfl <;>
        simp [blue, purple] at hne hcolor)

theorem sharedInteriorPairTaitEdgeColoring_isTait :
    IsTaitEdgeColoring sharedInteriorPairAnnulusGraph
      sharedInteriorPairTaitEdgeColoring := by
  intro e
  change sharedInteriorPairEdgeColor e ≠ 0
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph :
    ∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
      IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C := by
  exact
    ⟨sharedInteriorPairTaitEdgeColoring,
      sharedInteriorPairTaitEdgeColoring_isTait⟩

abbrev SharedInteriorPairFace := Fin 3

def sharedInteriorPairFaces : Finset SharedInteriorPairFace := Finset.univ

def sharedInteriorPairFaceBoundary :
    SharedInteriorPairFace → Finset sharedInteriorPairAnnulusGraph.edgeSet
  | ⟨0, _⟩ => {sip01, sip12, sip23, sip30}
  | ⟨1, _⟩ => {sip01, sip12, sip24, sip40}
  | ⟨2, _⟩ => {sip56, sip67, sip75}

theorem totalIncidenceCount_sip01 :
    totalIncidenceCount
        sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip01 = 2 := by
  decide

theorem totalIncidenceCount_sip12 :
    totalIncidenceCount
        sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip12 = 2 := by
  decide

theorem totalIncidenceCount_sip23 :
    totalIncidenceCount
        sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip23 = 1 := by
  decide

theorem totalIncidenceCount_sip30 :
    totalIncidenceCount
        sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip30 = 1 := by
  decide

theorem totalIncidenceCount_sip24 :
    totalIncidenceCount
        sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip24 = 1 := by
  decide

theorem totalIncidenceCount_sip40 :
    totalIncidenceCount
        sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip40 = 1 := by
  decide

theorem totalIncidenceCount_sip56 :
    totalIncidenceCount
        sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip56 = 1 := by
  decide

theorem totalIncidenceCount_sip67 :
    totalIncidenceCount
        sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip67 = 1 := by
  decide

theorem totalIncidenceCount_sip75 :
    totalIncidenceCount
        sharedInteriorPairFaceBoundary sharedInteriorPairFaces sip75 = 1 := by
  decide

def sharedInteriorPairAnnulusEmbedding :
    PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph where
  Face := SharedInteriorPairFace
  faceDecidableEq := inferInstance
  faces := sharedInteriorPairFaces
  faceBoundary := sharedInteriorPairFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases sharedInteriorPairAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases sharedInteriorPairAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

theorem sip23_mem_selectedBoundarySupport :
    sip23 ∈ selectedBoundarySupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces
      sharedInteriorPairAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip23⟩

theorem sip30_mem_selectedBoundarySupport :
    sip30 ∈ selectedBoundarySupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces
      sharedInteriorPairAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip30⟩

theorem sip24_mem_selectedBoundarySupport :
    sip24 ∈ selectedBoundarySupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces
      sharedInteriorPairAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip24⟩

theorem sip40_mem_selectedBoundarySupport :
    sip40 ∈ selectedBoundarySupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces
      sharedInteriorPairAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip40⟩

theorem sip56_mem_selectedBoundarySupport :
    sip56 ∈ selectedBoundarySupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces
      sharedInteriorPairAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip56⟩

theorem sip67_mem_selectedBoundarySupport :
    sip67 ∈ selectedBoundarySupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces
      sharedInteriorPairAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip67⟩

theorem sip75_mem_selectedBoundarySupport :
    sip75 ∈ selectedBoundarySupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces
      sharedInteriorPairAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip75⟩

theorem sip01_mem_interiorEdgeSupport :
    sip01 ∈ interiorEdgeSupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip01⟩

theorem sip12_mem_interiorEdgeSupport :
    sip12 ∈ interiorEdgeSupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_sip12⟩

theorem sip01_not_mem_selectedBoundarySupport :
    sip01 ∉ selectedBoundarySupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces
      sharedInteriorPairAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  rintro ⟨_, hcount⟩
  have hcount' :
      totalIncidenceCount
          sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces sip01 = 2 := by
    simpa [sharedInteriorPairAnnulusEmbedding] using totalIncidenceCount_sip01
  rw [hcount'] at hcount
  omega

theorem sip12_not_mem_selectedBoundarySupport :
    sip12 ∉ selectedBoundarySupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces
      sharedInteriorPairAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  rintro ⟨_, hcount⟩
  have hcount' :
      totalIncidenceCount
          sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces sip12 = 2 := by
    simpa [sharedInteriorPairAnnulusEmbedding] using totalIncidenceCount_sip12
  rw [hcount'] at hcount
  omega

def sipFace0 : AmbientFace sharedInteriorPairAnnulusEmbedding.faces :=
  ⟨(0 : SharedInteriorPairFace), by
    simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaces]⟩

def sipFace1 : AmbientFace sharedInteriorPairAnnulusEmbedding.faces :=
  ⟨(1 : SharedInteriorPairFace), by
    simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaces]⟩

def sipFace2 : AmbientFace sharedInteriorPairAnnulusEmbedding.faces :=
  ⟨(2 : SharedInteriorPairFace), by
    simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaces]⟩

theorem sipFace_cases
    (f : AmbientFace sharedInteriorPairAnnulusEmbedding.faces) :
    f = sipFace0 ∨ f = sipFace1 ∨ f = sipFace2 := by
  rcases f with ⟨⟨n, hn⟩, hfmem⟩
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by
    omega
  rcases hn_cases with rfl | rfl | rfl
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inl (Subtype.ext rfl)
  · exact Or.inr <| Or.inr (Subtype.ext rfl)

theorem sipFace0_ne_sipFace1 : sipFace0 ≠ sipFace1 := by
  intro h
  have hval : (0 : ℕ) = 1 := by
    simpa [sipFace0, sipFace1] using
      congrArg (fun f : AmbientFace sharedInteriorPairAnnulusEmbedding.faces => f.1.1) h
  omega

theorem sip01_mem_faceBoundary_iff
    (f : AmbientFace sharedInteriorPairAnnulusEmbedding.faces) :
    sip01 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f.1 ↔
      f = sipFace0 ∨ f = sipFace1 := by
  rcases sipFace_cases f with rfl | rfl | rfl <;>
    simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary,
      sipFace0, sipFace1, sipFace2, sip01, sip12, sip23, sip30, sip24, sip40,
      sip56, sip67, sip75, sharedInteriorPairAnnulusGraph]

theorem sip12_mem_faceBoundary_iff
    (f : AmbientFace sharedInteriorPairAnnulusEmbedding.faces) :
    sip12 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f.1 ↔
      f = sipFace0 ∨ f = sipFace1 := by
  rcases sipFace_cases f with rfl | rfl | rfl <;>
    simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary,
      sipFace0, sipFace1, sipFace2, sip01, sip12, sip23, sip30, sip24, sip40,
      sip56, sip67, sip75, sharedInteriorPairAnnulusGraph]

theorem sip12_mem_faceBoundary_of_sip01_mem
    {f : AmbientFace sharedInteriorPairAnnulusEmbedding.faces}
    (hf : sip01 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f.1) :
    sip12 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f.1 := by
  exact (sip12_mem_faceBoundary_iff f).2 ((sip01_mem_faceBoundary_iff f).1 hf)

theorem sip01_mem_faceBoundary_of_sip12_mem
    {f : AmbientFace sharedInteriorPairAnnulusEmbedding.faces}
    (hf : sip12 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f.1) :
    sip01 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f.1 := by
  exact (sip01_mem_faceBoundary_iff f).2 ((sip12_mem_faceBoundary_iff f).1 hf)

def sipDart01 : sharedInteriorPairAnnulusGraph.Dart := ⟨((0 : Fin 8), 1), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sipDart12 : sharedInteriorPairAnnulusGraph.Dart := ⟨((1 : Fin 8), 2), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sipDart23 : sharedInteriorPairAnnulusGraph.Dart := ⟨((2 : Fin 8), 3), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sipDart30 : sharedInteriorPairAnnulusGraph.Dart := ⟨((3 : Fin 8), 0), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sipDart24 : sharedInteriorPairAnnulusGraph.Dart := ⟨((2 : Fin 8), 4), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sipDart40 : sharedInteriorPairAnnulusGraph.Dart := ⟨((4 : Fin 8), 0), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sipDart56 : sharedInteriorPairAnnulusGraph.Dart := ⟨((5 : Fin 8), 6), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sipDart67 : sharedInteriorPairAnnulusGraph.Dart := ⟨((6 : Fin 8), 7), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sipDart75 : sharedInteriorPairAnnulusGraph.Dart := ⟨((7 : Fin 8), 5), by
  simp [sharedInteriorPairAnnulusGraph]⟩

def sipFace0PureDartCycle
    (hf : (0 : SharedInteriorPairFace) ∈ sharedInteriorPairAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      sharedInteriorPairAnnulusEmbedding ⟨(0 : SharedInteriorPairFace), hf⟩ where
  darts := [sipDart01, sipDart12, sipDart23, sipDart30]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, sipDart01, sipDart12, sipDart23, sipDart30]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary,
        sip01, sip12, sip23, sip30, sipDart01, sipDart12, sipDart23, sipDart30]
  hface_sub := by
    intro e he
    have he' : e = sip01 ∨ e = sip12 ∨ e = sip23 ∨ e = sip30 := by
      simpa [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [sip01, sip12, sip23, sip30,
        sipDart01, sipDart12, sipDart23, sipDart30]

def sipFace1PureDartCycle
    (hf : (1 : SharedInteriorPairFace) ∈ sharedInteriorPairAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      sharedInteriorPairAnnulusEmbedding ⟨(1 : SharedInteriorPairFace), hf⟩ where
  darts := [sipDart01, sipDart12, sipDart24, sipDart40]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, sipDart01, sipDart12, sipDart24, sipDart40]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary,
        sip01, sip12, sip24, sip40, sipDart01, sipDart12, sipDart24, sipDart40]
  hface_sub := by
    intro e he
    have he' : e = sip01 ∨ e = sip12 ∨ e = sip24 ∨ e = sip40 := by
      simpa [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary] using he
    rcases he' with rfl | rfl | rfl | rfl <;>
      simp [sip01, sip12, sip24, sip40,
        sipDart01, sipDart12, sipDart24, sipDart40]

def sipFace2PureDartCycle
    (hf : (2 : SharedInteriorPairFace) ∈ sharedInteriorPairAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      sharedInteriorPairAnnulusEmbedding ⟨(2 : SharedInteriorPairFace), hf⟩ where
  darts := [sipDart56, sipDart67, sipDart75]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, sipDart56, sipDart67, sipDart75]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary,
        sip56, sip67, sip75, sipDart56, sipDart67, sipDart75]
  hface_sub := by
    intro e he
    have he' : e = sip56 ∨ e = sip67 ∨ e = sip75 := by
      simpa [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [sip56, sip67, sip75, sipDart56, sipDart67, sipDart75]

def sharedInteriorPairPureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry
      sharedInteriorPairAnnulusEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change SharedInteriorPairFace at f
    by_cases h0 : f = (0 : SharedInteriorPairFace)
    · subst f
      exact sipFace0PureDartCycle hfmem
    · by_cases h1 : f = (1 : SharedInteriorPairFace)
      · subst f
        exact sipFace1PureDartCycle hfmem
      · have h2 : f = (2 : SharedInteriorPairFace) := by
          fin_cases f
          · exact False.elim (h0 rfl)
          · exact False.elim (h1 rfl)
          · rfl
        subst f
        exact sipFace2PureDartCycle hfmem

def sipFace0DartSuccessor (d : sharedInteriorPairAnnulusGraph.Dart) :
    sharedInteriorPairAnnulusGraph.Dart :=
  if d = sipDart01 then sipDart12
  else if d = sipDart12 then sipDart23
  else if d = sipDart23 then sipDart30
  else sipDart01

def sipFace1DartSuccessor (d : sharedInteriorPairAnnulusGraph.Dart) :
    sharedInteriorPairAnnulusGraph.Dart :=
  if d = sipDart01 then sipDart12
  else if d = sipDart12 then sipDart24
  else if d = sipDart24 then sipDart40
  else sipDart01

def sipFace2DartSuccessor (d : sharedInteriorPairAnnulusGraph.Dart) :
    sharedInteriorPairAnnulusGraph.Dart :=
  if d = sipDart56 then sipDart67
  else if d = sipDart67 then sipDart75
  else sipDart56

def sipFace0DartSuccessorCycle
    (hf : (0 : SharedInteriorPairFace) ∈ sharedInteriorPairAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      sharedInteriorPairAnnulusEmbedding ⟨(0 : SharedInteriorPairFace), hf⟩ where
  darts := [sipDart01, sipDart12, sipDart23, sipDart30]
  hnonempty := by simp
  successor := sipFace0DartSuccessor
  hsuccessor_order := by
    simp [sipFace0DartSuccessor, sipDart01, sipDart12, sipDart23, sipDart30]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, sipFace0DartSuccessor, sipDart01, sipDart12,
        sipDart23, sipDart30]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (sipFace0PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (sipFace0PureDartCycle hf).hface_sub e he

def sipFace1DartSuccessorCycle
    (hf : (1 : SharedInteriorPairFace) ∈ sharedInteriorPairAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      sharedInteriorPairAnnulusEmbedding ⟨(1 : SharedInteriorPairFace), hf⟩ where
  darts := [sipDart01, sipDart12, sipDart24, sipDart40]
  hnonempty := by simp
  successor := sipFace1DartSuccessor
  hsuccessor_order := by
    simp [sipFace1DartSuccessor, sipDart01, sipDart12, sipDart24, sipDart40]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, sipFace1DartSuccessor, sipDart01, sipDart12,
        sipDart24, sipDart40]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (sipFace1PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (sipFace1PureDartCycle hf).hface_sub e he

def sipFace2DartSuccessorCycle
    (hf : (2 : SharedInteriorPairFace) ∈ sharedInteriorPairAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycle
      sharedInteriorPairAnnulusEmbedding ⟨(2 : SharedInteriorPairFace), hf⟩ where
  darts := [sipDart56, sipDart67, sipDart75]
  hnonempty := by simp
  successor := sipFace2DartSuccessor
  hsuccessor_order := by
    simp [sipFace2DartSuccessor, sipDart56, sipDart67, sipDart75]
  hsuccessor_adj := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [SimpleGraph.DartAdj, sipFace2DartSuccessor, sipDart56, sipDart67,
        sipDart75]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    exact (sipFace2PureDartCycle hf).hedge_sub d hd
  hface_sub := by
    intro e he
    exact (sipFace2PureDartCycle hf).hface_sub e he

def sharedInteriorPairDartSuccessorCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryDartSuccessorCycleGeometry
      sharedInteriorPairAnnulusEmbedding where
  faceBoundaryDartSuccessorCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change SharedInteriorPairFace at f
    by_cases h0 : f = (0 : SharedInteriorPairFace)
    · subst f
      exact sipFace0DartSuccessorCycle hfmem
    · by_cases h1 : f = (1 : SharedInteriorPairFace)
      · subst f
        exact sipFace1DartSuccessorCycle hfmem
      · have h2 : f = (2 : SharedInteriorPairFace) := by
          fin_cases f
          · exact False.elim (h0 rfl)
          · exact False.elim (h1 rfl)
          · rfl
        subst f
        exact sipFace2DartSuccessorCycle hfmem

theorem nonempty_sharedInteriorPairDartSuccessorCycleGeometry :
    Nonempty
      (PlanarBoundaryDartSuccessorCycleEmbeddingData
        sharedInteriorPairAnnulusEmbedding) :=
  ⟨sharedInteriorPairDartSuccessorCycleGeometry⟩

def sharedInteriorPairClosedWalkEmbeddingData :
    PlanarBoundaryClosedWalkEmbeddingData sharedInteriorPairAnnulusEmbedding :=
  sharedInteriorPairPureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

theorem sharedInteriorPairClosedWalkEmbeddingData_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace sharedInteriorPairAnnulusEmbedding.faces,
      (sharedInteriorPairClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f := by
  intro f
  have hf_cases : f = sipFace0 ∨ f = sipFace1 ∨ f = sipFace2 := by
    rcases f with ⟨⟨n, hn⟩, hfmem⟩
    have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn_cases with rfl | rfl | rfl
    · exact Or.inl (Subtype.ext rfl)
    · exact Or.inr <| Or.inl (Subtype.ext rfl)
    · exact Or.inr <| Or.inr (Subtype.ext rfl)
  rcases hf_cases with hf0 | hf12
  · subst hf0
    refine ⟨[sip23, sip30], ?_, ?_⟩
    · decide
    · intro e
      rcases sharedInteriorPairAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · rcases hf12 with hf1 | hf2
    · subst hf1
      refine ⟨[sip24, sip40], ?_, ?_⟩
      · decide
      · intro e
        rcases sharedInteriorPairAnnulus_edge_eq e with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide
    · subst hf2
      refine ⟨[sip56, sip67, sip75], ?_, ?_⟩
      · decide
      · intro e
        rcases sharedInteriorPairAnnulus_edge_eq e with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide

theorem sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace sharedInteriorPairAnnulusEmbedding.faces,
      (PlanarBoundaryDartSuccessorCycleEmbeddingData.toPlanarBoundaryClosedWalkEmbeddingData
        sharedInteriorPairDartSuccessorCycleGeometry
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f := by
  intro f
  have hf_cases : f = sipFace0 ∨ f = sipFace1 ∨ f = sipFace2 := by
    rcases f with ⟨⟨n, hn⟩, hfmem⟩
    have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hn_cases with rfl | rfl | rfl
    · exact Or.inl (Subtype.ext rfl)
    · exact Or.inr <| Or.inl (Subtype.ext rfl)
    · exact Or.inr <| Or.inr (Subtype.ext rfl)
  rcases hf_cases with hf0 | hf12
  · subst hf0
    refine ⟨[sip23, sip30], ?_, ?_⟩
    · decide
    · intro e
      rcases sharedInteriorPairAnnulus_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · rcases hf12 with hf1 | hf2
    · subst hf1
      refine ⟨[sip24, sip40], ?_, ?_⟩
      · decide
      · intro e
        rcases sharedInteriorPairAnnulus_edge_eq e with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide
    · subst hf2
      refine ⟨[sip56, sip67, sip75], ?_, ?_⟩
      · decide
      · intro e
        rcases sharedInteriorPairAnnulus_edge_eq e with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide

def sipOuterRoot : PlanarBoundaryEdgeVertex sharedInteriorPairAnnulusEmbedding :=
  ⟨sip23, sip23_mem_selectedBoundarySupport⟩

def sipInnerRoot : PlanarBoundaryEdgeVertex sharedInteriorPairAnnulusEmbedding :=
  ⟨sip56, sip56_mem_selectedBoundarySupport⟩

def sipBoundaryLabel
    (e : PlanarBoundaryEdgeVertex sharedInteriorPairAnnulusEmbedding) : Bool :=
  if e.1 = sip56 ∨ e.1 = sip67 ∨ e.1 = sip75 then true else false

theorem sip_boundaryEdge_eq
    (e : PlanarBoundaryEdgeVertex sharedInteriorPairAnnulusEmbedding) :
    e = ⟨sip23, sip23_mem_selectedBoundarySupport⟩ ∨
      e = ⟨sip30, sip30_mem_selectedBoundarySupport⟩ ∨
      e = ⟨sip24, sip24_mem_selectedBoundarySupport⟩ ∨
      e = ⟨sip40, sip40_mem_selectedBoundarySupport⟩ ∨
      e = ⟨sip56, sip56_mem_selectedBoundarySupport⟩ ∨
      e = ⟨sip67, sip67_mem_selectedBoundarySupport⟩ ∨
      e = ⟨sip75, sip75_mem_selectedBoundarySupport⟩ := by
  rcases sharedInteriorPairAnnulus_edge_eq e.1 with
    h01 | h12 | h23 | h30 | h24 | h40 | h56 | h67 | h75
  · exact False.elim (sip01_not_mem_selectedBoundarySupport (by simpa [h01] using e.2))
  · exact False.elim (sip12_not_mem_selectedBoundarySupport (by simpa [h12] using e.2))
  · exact Or.inl (Subtype.ext h23)
  · exact Or.inr <| Or.inl (Subtype.ext h30)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h24)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h40)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h56)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h67)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      (Subtype.ext h75)

theorem vertex_one_mem_selectedBoundaryInteriorEdgeEndpointVertices_sharedInteriorPair :
    (1 : Fin 8) ∈
      selectedBoundaryInteriorEdgeEndpointVertices sharedInteriorPairAnnulusEmbedding := by
  rw [mem_selectedBoundaryInteriorEdgeEndpointVertices_iff]
  constructor
  · exact ⟨sip01, sip01_mem_interiorEdgeSupport, by simp [sip01]⟩
  · intro e he
    rcases sip_boundaryEdge_eq ⟨e, he⟩ with
      h23 | h30 | h24 | h40 | h56 | h67 | h75
    · have heq : e = sip23 := congrArg Subtype.val h23
      subst e
      simp [sip23]
    · have heq : e = sip30 := congrArg Subtype.val h30
      subst e
      simp [sip30]
    · have heq : e = sip24 := congrArg Subtype.val h24
      subst e
      simp [sip24]
    · have heq : e = sip40 := congrArg Subtype.val h40
      subst e
      simp [sip40]
    · have heq : e = sip56 := congrArg Subtype.val h56
      subst e
      simp [sip56]
    · have heq : e = sip67 := congrArg Subtype.val h67
      subst e
      simp [sip67]
    · have heq : e = sip75 := congrArg Subtype.val h75
      subst e
      simp [sip75]

theorem selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair :
    (selectedBoundaryInteriorEdgeEndpointVertices
      sharedInteriorPairAnnulusEmbedding).Nonempty :=
  ⟨1, vertex_one_mem_selectedBoundaryInteriorEdgeEndpointVertices_sharedInteriorPair⟩

theorem sipBoundaryAdj_preserves_label :
    ∀ ⦃e f : PlanarBoundaryEdgeVertex sharedInteriorPairAnnulusEmbedding⦄,
      (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Adj e f →
        sipBoundaryLabel e = sipBoundaryLabel f := by
  intro e f hadj
  rcases sip_boundaryEdge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases sip_boundaryEdge_eq f with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact False.elim
          (by
            rcases hadj with ⟨_, v, hvE, hvF⟩
            fin_cases v <;>
              simp [sip23, sip30, sip24, sip40, sip56, sip67, sip75] at hvE hvF)

theorem sipOuterRoot_ne_innerRoot : sipOuterRoot ≠ sipInnerRoot := by
  intro h
  have := congrArg Subtype.val h
  simp [sipOuterRoot, sipInnerRoot, sip23, sip56] at this

theorem sip30_reachable_outerRoot :
    (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Reachable
      ⟨sip30, sip30_mem_selectedBoundarySupport⟩ sipOuterRoot := by
  have hadj :
      (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Adj
        ⟨sip30, sip30_mem_selectedBoundarySupport⟩ sipOuterRoot := by
    refine ⟨?_, 3, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp [sipOuterRoot, sip30, sip23] at this
    · simp [sip30]
    · simp [sipOuterRoot, sip23]
  exact hadj.reachable

theorem sip24_reachable_outerRoot :
    (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Reachable
      ⟨sip24, sip24_mem_selectedBoundarySupport⟩ sipOuterRoot := by
  have hadj :
      (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Adj
        ⟨sip24, sip24_mem_selectedBoundarySupport⟩ sipOuterRoot := by
    refine ⟨?_, 2, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp [sipOuterRoot, sip24, sip23] at this
    · simp [sip24]
    · simp [sipOuterRoot, sip23]
  exact hadj.reachable

theorem sip40_reachable_outerRoot :
    (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Reachable
      ⟨sip40, sip40_mem_selectedBoundarySupport⟩ sipOuterRoot := by
  have h40_30 :
      (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Reachable
        ⟨sip40, sip40_mem_selectedBoundarySupport⟩
        ⟨sip30, sip30_mem_selectedBoundarySupport⟩ := by
    have hadj :
        (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Adj
          ⟨sip40, sip40_mem_selectedBoundarySupport⟩
          ⟨sip30, sip30_mem_selectedBoundarySupport⟩ := by
      refine ⟨?_, 0, ?_, ?_⟩
      · intro h
        have := congrArg Subtype.val h
        simp [sip40, sip30] at this
      · simp [sip40]
      · simp [sip30]
    exact hadj.reachable
  exact h40_30.trans sip30_reachable_outerRoot

theorem sip67_reachable_innerRoot :
    (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Reachable
      ⟨sip67, sip67_mem_selectedBoundarySupport⟩ sipInnerRoot := by
  have hadj :
      (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Adj
        ⟨sip67, sip67_mem_selectedBoundarySupport⟩ sipInnerRoot := by
    refine ⟨?_, 6, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp [sipInnerRoot, sip67, sip56] at this
    · simp [sip67]
    · simp [sipInnerRoot, sip56]
  exact hadj.reachable

theorem sip75_reachable_innerRoot :
    (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Reachable
      ⟨sip75, sip75_mem_selectedBoundarySupport⟩ sipInnerRoot := by
  have hadj :
      (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Adj
        ⟨sip75, sip75_mem_selectedBoundarySupport⟩ sipInnerRoot := by
    refine ⟨?_, 5, ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp [sipInnerRoot, sip75, sip56] at this
    · simp [sip75]
    · simp [sipInnerRoot, sip56]
  exact hadj.reachable

def sharedInteriorPairAnnulusBoundaryReachabilityData :
    PlanarBoundaryAnnulusBoundaryReachabilityData sharedInteriorPairAnnulusEmbedding where
  outerRoot := sipOuterRoot
  innerRoot := sipInnerRoot
  hroots_ne := sipOuterRoot_ne_innerRoot
  hcoverRoots := by
    intro e
    rcases sip_boundaryEdge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨sipOuterRoot, by simp [sipOuterRoot_ne_innerRoot], SimpleGraph.Reachable.refl _⟩
    · refine ⟨sipOuterRoot, by simp [sipOuterRoot_ne_innerRoot], ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Adj
            ⟨sip30, sip30_mem_selectedBoundarySupport⟩ sipOuterRoot := by
        refine ⟨?_, 3, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [sipOuterRoot, sip30, sip23] at this
        · simp [sip30]
        · simp [sipOuterRoot, sip23]
      exact hadj.reachable
    · refine ⟨sipOuterRoot, by simp [sipOuterRoot_ne_innerRoot], ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Adj
            ⟨sip24, sip24_mem_selectedBoundarySupport⟩ sipOuterRoot := by
        refine ⟨?_, 2, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [sipOuterRoot, sip24, sip23] at this
        · simp [sip24]
        · simp [sipOuterRoot, sip23]
      exact hadj.reachable
    · refine ⟨sipOuterRoot, by simp [sipOuterRoot_ne_innerRoot], ?_⟩
      have h40_30 :
          (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Reachable
            ⟨sip40, sip40_mem_selectedBoundarySupport⟩
            ⟨sip30, sip30_mem_selectedBoundarySupport⟩ := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Adj
              ⟨sip40, sip40_mem_selectedBoundarySupport⟩
              ⟨sip30, sip30_mem_selectedBoundarySupport⟩ := by
          refine ⟨?_, 0, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [sip40, sip30] at this
          · simp [sip40]
          · simp [sip30]
        exact hadj.reachable
      have h30_outer :
          (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Reachable
            ⟨sip30, sip30_mem_selectedBoundarySupport⟩ sipOuterRoot := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Adj
              ⟨sip30, sip30_mem_selectedBoundarySupport⟩ sipOuterRoot := by
          refine ⟨?_, 3, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [sipOuterRoot, sip30, sip23] at this
          · simp [sip30]
          · simp [sipOuterRoot, sip23]
        exact hadj.reachable
      exact h40_30.trans h30_outer
    · refine ⟨sipInnerRoot, by simp, SimpleGraph.Reachable.refl _⟩
    · refine ⟨sipInnerRoot, by simp, ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Adj
            ⟨sip67, sip67_mem_selectedBoundarySupport⟩ sipInnerRoot := by
        refine ⟨?_, 6, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [sipInnerRoot, sip67, sip56] at this
        · simp [sip67]
        · simp [sipInnerRoot, sip56]
      exact hadj.reachable
    · refine ⟨sipInnerRoot, by simp, ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Adj
            ⟨sip75, sip75_mem_selectedBoundarySupport⟩ sipInnerRoot := by
        refine ⟨?_, 5, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [sipInnerRoot, sip75, sip56] at this
        · simp [sip75]
        · simp [sipInnerRoot, sip56]
      exact hadj.reachable
  hsepRoots := by
    intro r s hr hs hreach
    have hlabelEq :
        sipBoundaryLabel r = sipBoundaryLabel s :=
      eq_of_reachable_of_eq_on_adj
        (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding)
        sipBoundaryLabel
        (by
          intro u v huv
          exact sipBoundaryAdj_preserves_label huv)
        hreach
    have hOuterLabel : sipBoundaryLabel sipOuterRoot = false := by
      decide
    have hInnerLabel : sipBoundaryLabel sipInnerRoot = true := by
      decide
    have hr_cases : r = sipOuterRoot ∨ r = sipInnerRoot := by
      simpa [sipOuterRoot_ne_innerRoot] using hr
    have hs_cases : s = sipOuterRoot ∨ s = sipInnerRoot := by
      simpa [sipOuterRoot_ne_innerRoot] using hs
    rcases hr_cases with rfl | rfl <;> rcases hs_cases with rfl | rfl
    · rfl
    · rw [hOuterLabel, hInnerLabel] at hlabelEq
      cases hlabelEq
    · rw [hInnerLabel, hOuterLabel] at hlabelEq
      cases hlabelEq
    · rfl

def sharedInteriorPairClosedWalkAnnulusBoundarySource :
    PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields
    sharedInteriorPairAnnulusBoundaryReachabilityData
    sharedInteriorPairClosedWalkEmbeddingData
    sharedInteriorPairClosedWalkEmbeddingData_selectedBoundaryArcOnFace

def sharedInteriorPairDartSuccessorClosedWalkAnnulusBoundarySource :
    PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
    sharedInteriorPairAnnulusBoundaryReachabilityData
    sharedInteriorPairDartSuccessorCycleGeometry
    sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace

theorem nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource :
    Nonempty
      (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) :=
  ⟨sharedInteriorPairClosedWalkAnnulusBoundarySource⟩

theorem nonempty_sharedInteriorPairDartSuccessorClosedWalkAnnulusBoundarySource :
    Nonempty
      (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) :=
  ⟨sharedInteriorPairDartSuccessorClosedWalkAnnulusBoundarySource⟩

theorem sharedInteriorPairGraph_admitsPlanarBoundaryClosedWalkAnnulusBoundarySource :
    AdmitsPlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusGraph := by
  exact ⟨sharedInteriorPairAnnulusEmbedding,
    nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource⟩

theorem sharedInteriorPairGraph_admitsPlanarBoundaryDartSuccessorCycleEmbeddingData :
    AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData sharedInteriorPairAnnulusGraph := by
  exact ⟨sharedInteriorPairAnnulusEmbedding,
    nonempty_sharedInteriorPairDartSuccessorCycleGeometry⟩

theorem exists_two_distinct_interior_edges_on_sipFace0_boundary :
    ∃ e₁ ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1,
      ∃ e₂ ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1,
        e₁ ≠ e₂ ∧
          e₁ ∈ interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces ∧
            e₂ ∈ interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
              sharedInteriorPairAnnulusEmbedding.faces := by
  refine ⟨sip01, by simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary,
      sipFace0], sip12, by simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary,
      sipFace0], sip01_ne_sip12, sip01_mem_interiorEdgeSupport, sip12_mem_interiorEdgeSupport⟩

theorem exists_two_distinct_interior_edges_on_sipFace1_boundary :
    ∃ e₁ ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace1.1,
      ∃ e₂ ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace1.1,
        e₁ ≠ e₂ ∧
          e₁ ∈ interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces ∧
            e₂ ∈ interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
              sharedInteriorPairAnnulusEmbedding.faces := by
  refine ⟨sip01, by simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary,
      sipFace1], sip12, by simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary,
      sipFace1], sip01_ne_sip12, sip01_mem_interiorEdgeSupport, sip12_mem_interiorEdgeSupport⟩

/-- The shared-interior-pair source visibly violates the local at-most-one-interior-edge
premise on `sipFace0`: its face boundary filters to the two shared interior edges `sip01`
and `sip12`. -/
theorem sharedInteriorPair_sipFace0_interiorEdgeFilter_card :
    ((sharedInteriorPairAnnulusEmbedding.faceBoundary sipFace0.1).filter
        (· ∈ interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces)).card = 2 := by
  decide

/-- The honest shared-interior-pair annulus embedding cannot satisfy the local at-most-one
interior edge per face premise used by the canonical-witness constructors. -/
theorem not_sharedInteriorPair_atMostOneInteriorEdgePerFace :
    ¬ ∀ f : AmbientFace sharedInteriorPairAnnulusEmbedding.faces,
      ((sharedInteriorPairAnnulusEmbedding.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces)).card ≤ 1 := by
  intro hAtMost
  have h0 := hAtMost sipFace0
  rw [sharedInteriorPair_sipFace0_interiorEdgeFilter_card] at h0
  omega

noncomputable def sharedInteriorPairBoundaryData :
    PlanarBoundaryAnnulusBoundaryData sharedInteriorPairAnnulusEmbedding :=
  sharedInteriorPairClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData

theorem sipOuterRoot_uniqueReachableRoot_eq :
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding)
        sharedInteriorPairAnnulusBoundaryReachabilityData.rootSet
        sharedInteriorPairAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        sipOuterRoot = sipOuterRoot := by
  let T := planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding
  let roots := sharedInteriorPairAnnulusBoundaryReachabilityData.rootSet
  let hroots := sharedInteriorPairAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
  apply (hroots sipOuterRoot).unique
  · exact ⟨uniqueReachableRoot_mem_roots T roots hroots sipOuterRoot,
      reachable_uniqueReachableRoot T roots hroots sipOuterRoot⟩
  · exact ⟨by
        change sipOuterRoot ∈ ({sipOuterRoot, sipInnerRoot} :
          Finset (PlanarBoundaryEdgeVertex sharedInteriorPairAnnulusEmbedding))
        simp,
      SimpleGraph.Reachable.refl _⟩

theorem sipInnerRoot_uniqueReachableRoot_eq :
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding)
        sharedInteriorPairAnnulusBoundaryReachabilityData.rootSet
        sharedInteriorPairAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        sipInnerRoot = sipInnerRoot := by
  let T := planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding
  let roots := sharedInteriorPairAnnulusBoundaryReachabilityData.rootSet
  let hroots := sharedInteriorPairAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
  apply (hroots sipInnerRoot).unique
  · exact ⟨uniqueReachableRoot_mem_roots T roots hroots sipInnerRoot,
      reachable_uniqueReachableRoot T roots hroots sipInnerRoot⟩
  · exact ⟨by
        change sipInnerRoot ∈ ({sipOuterRoot, sipInnerRoot} :
          Finset (PlanarBoundaryEdgeVertex sharedInteriorPairAnnulusEmbedding))
        simp,
      SimpleGraph.Reachable.refl _⟩

theorem uniqueReachableRoot_eq_sipOuterRoot_of_reachable
    {e : PlanarBoundaryEdgeVertex sharedInteriorPairAnnulusEmbedding}
    (hreach :
      (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Reachable
        e sipOuterRoot) :
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding)
        sharedInteriorPairAnnulusBoundaryReachabilityData.rootSet
        sharedInteriorPairAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        e = sipOuterRoot := by
  calc
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding)
        sharedInteriorPairAnnulusBoundaryReachabilityData.rootSet
        sharedInteriorPairAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        e =
      uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding)
        sharedInteriorPairAnnulusBoundaryReachabilityData.rootSet
        sharedInteriorPairAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        sipOuterRoot := by
          exact
            uniqueReachableRoot_eq_of_reachable
              (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding)
              sharedInteriorPairAnnulusBoundaryReachabilityData.rootSet
              sharedInteriorPairAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
              hreach
    _ = sipOuterRoot := sipOuterRoot_uniqueReachableRoot_eq

theorem uniqueReachableRoot_eq_sipInnerRoot_of_reachable
    {e : PlanarBoundaryEdgeVertex sharedInteriorPairAnnulusEmbedding}
    (hreach :
      (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding).Reachable
        e sipInnerRoot) :
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding)
        sharedInteriorPairAnnulusBoundaryReachabilityData.rootSet
        sharedInteriorPairAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        e = sipInnerRoot := by
  calc
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding)
        sharedInteriorPairAnnulusBoundaryReachabilityData.rootSet
        sharedInteriorPairAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        e =
      uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding)
        sharedInteriorPairAnnulusBoundaryReachabilityData.rootSet
        sharedInteriorPairAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
        sipInnerRoot := by
          exact
            uniqueReachableRoot_eq_of_reachable
              (planarBoundarySupportEndpointAdjGraph sharedInteriorPairAnnulusEmbedding)
              sharedInteriorPairAnnulusBoundaryReachabilityData.rootSet
              sharedInteriorPairAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
              hreach
    _ = sipInnerRoot := sipInnerRoot_uniqueReachableRoot_eq

theorem sip23_mem_sharedInteriorPairOuterAmbientBoundary :
    sip23 ∈ sharedInteriorPairBoundaryData.outerAmbientBoundary := by
  exact
    by
      simpa [sharedInteriorPairBoundaryData, sipOuterRoot] using
        PlanarBoundaryAnnulusBoundaryReachabilityData.mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
          (data := sharedInteriorPairAnnulusBoundaryReachabilityData)
          (e := sipOuterRoot) sipOuterRoot_uniqueReachableRoot_eq

theorem sip24_mem_sharedInteriorPairOuterAmbientBoundary :
    sip24 ∈ sharedInteriorPairBoundaryData.outerAmbientBoundary := by
  exact
    by
      simpa [sharedInteriorPairBoundaryData] using
        PlanarBoundaryAnnulusBoundaryReachabilityData.mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
          (data := sharedInteriorPairAnnulusBoundaryReachabilityData)
          (e := ⟨sip24, sip24_mem_selectedBoundarySupport⟩)
          (uniqueReachableRoot_eq_sipOuterRoot_of_reachable sip24_reachable_outerRoot)

theorem sip56_mem_sharedInteriorPairInnerAmbientBoundary :
    sip56 ∈ sharedInteriorPairBoundaryData.innerAmbientBoundary := by
  exact
    by
      simpa [sharedInteriorPairBoundaryData, sipInnerRoot] using
        PlanarBoundaryAnnulusBoundaryReachabilityData.mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
          (data := sharedInteriorPairAnnulusBoundaryReachabilityData)
          (e := sipInnerRoot) sipInnerRoot_uniqueReachableRoot_eq

theorem sip67_mem_sharedInteriorPairInnerAmbientBoundary :
    sip67 ∈ sharedInteriorPairBoundaryData.innerAmbientBoundary := by
  exact
    by
      simpa [sharedInteriorPairBoundaryData] using
        PlanarBoundaryAnnulusBoundaryReachabilityData.mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
          (data := sharedInteriorPairAnnulusBoundaryReachabilityData)
          (e := ⟨sip67, sip67_mem_selectedBoundarySupport⟩)
          (uniqueReachableRoot_eq_sipInnerRoot_of_reachable sip67_reachable_innerRoot)

theorem sip75_mem_sharedInteriorPairInnerAmbientBoundary :
    sip75 ∈ sharedInteriorPairBoundaryData.innerAmbientBoundary := by
  exact
    by
      simpa [sharedInteriorPairBoundaryData] using
        PlanarBoundaryAnnulusBoundaryReachabilityData.mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
          (data := sharedInteriorPairAnnulusBoundaryReachabilityData)
          (e := ⟨sip75, sip75_mem_selectedBoundarySupport⟩)
          (uniqueReachableRoot_eq_sipInnerRoot_of_reachable sip75_reachable_innerRoot)

theorem sip23_not_mem_sharedInteriorPairInnerAmbientBoundary :
    sip23 ∉ sharedInteriorPairBoundaryData.innerAmbientBoundary := by
  intro hinner
  exact
    (Finset.disjoint_left.mp sharedInteriorPairBoundaryData.hambientBoundaryDisjoint)
      sip23_mem_sharedInteriorPairOuterAmbientBoundary hinner

theorem sip24_not_mem_sharedInteriorPairInnerAmbientBoundary :
    sip24 ∉ sharedInteriorPairBoundaryData.innerAmbientBoundary := by
  intro hinner
  exact
    (Finset.disjoint_left.mp sharedInteriorPairBoundaryData.hambientBoundaryDisjoint)
      sip24_mem_sharedInteriorPairOuterAmbientBoundary hinner

theorem sip23_mem_relativeBoundarySupport_of_sipFace0_mem
    {S : Finset (AmbientFace sharedInteriorPairAnnulusEmbedding.faces)}
    (h0 : sipFace0 ∈ S) :
    sip23 ∈ relativeBoundarySupport
      (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
        sharedInteriorPairAnnulusEmbedding.faceBoundary) S := by
  refine
    (mem_relativeBoundarySupport_iff
      (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
        sharedInteriorPairAnnulusEmbedding.faceBoundary) S).2 ?_
  constructor
  · exact Finset.mem_biUnion.2
      ⟨sipFace0, h0, by
        simp [ambientFaceBoundary, sharedInteriorPairAnnulusEmbedding,
          sharedInteriorPairFaceBoundary, sipFace0, sip23]⟩
  · unfold subsetIncidenceCount
    have hfilter :
        S.filter
            (fun f =>
              sip23 ∈
                ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
                  sharedInteriorPairAnnulusEmbedding.faceBoundary f) = {sipFace0} := by
      ext f
      constructor
      · intro hf
        have hfS : f ∈ S := (Finset.mem_filter.1 hf).1
        have hfe :
            sip23 ∈
              ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
                sharedInteriorPairAnnulusEmbedding.faceBoundary f :=
          (Finset.mem_filter.1 hf).2
        rcases sipFace_cases f with rfl | rfl | rfl
        · simp
        · simp [ambientFaceBoundary, sharedInteriorPairAnnulusEmbedding,
            sharedInteriorPairFaceBoundary, sipFace1, sip24] at hfe
          have : False := by
            simp [sip23, sip01, sip12, sip40] at hfe
          exact False.elim this
        · simp [ambientFaceBoundary, sharedInteriorPairAnnulusEmbedding,
            sharedInteriorPairFaceBoundary, sipFace2, sip56, sip67, sip75] at hfe
          have : False := by
            simp [sip23] at hfe
          exact False.elim this
      · intro hf
        have hf0 : f = sipFace0 := by
          simpa using hf
        subst hf0
        exact Finset.mem_filter.2 ⟨h0, by
          simp [ambientFaceBoundary, sharedInteriorPairAnnulusEmbedding,
            sharedInteriorPairFaceBoundary, sipFace0, sip23]⟩
    simp [hfilter]

theorem sip24_mem_relativeBoundarySupport_of_sipFace1_mem
    {S : Finset (AmbientFace sharedInteriorPairAnnulusEmbedding.faces)}
    (h1 : sipFace1 ∈ S) :
    sip24 ∈ relativeBoundarySupport
      (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
        sharedInteriorPairAnnulusEmbedding.faceBoundary) S := by
  refine
    (mem_relativeBoundarySupport_iff
      (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
        sharedInteriorPairAnnulusEmbedding.faceBoundary) S).2 ?_
  constructor
  · exact Finset.mem_biUnion.2
      ⟨sipFace1, h1, by
        simp [ambientFaceBoundary, sharedInteriorPairAnnulusEmbedding,
          sharedInteriorPairFaceBoundary, sipFace1, sip24]⟩
  · unfold subsetIncidenceCount
    have hfilter :
        S.filter
            (fun f =>
              sip24 ∈
                ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
                  sharedInteriorPairAnnulusEmbedding.faceBoundary f) = {sipFace1} := by
      ext f
      constructor
      · intro hf
        have hfe :
            sip24 ∈
              ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
                sharedInteriorPairAnnulusEmbedding.faceBoundary f :=
          (Finset.mem_filter.1 hf).2
        rcases sipFace_cases f with rfl | rfl | rfl
        · simp [ambientFaceBoundary, sharedInteriorPairAnnulusEmbedding,
            sharedInteriorPairFaceBoundary, sipFace0, sip23, sip30] at hfe
          have : False := by
            simp [sip24, sip01, sip12] at hfe
          exact False.elim this
        · simp
        · simp [ambientFaceBoundary, sharedInteriorPairAnnulusEmbedding,
            sharedInteriorPairFaceBoundary, sipFace2, sip56, sip67, sip75] at hfe
          have : False := by
            simp [sip24] at hfe
          exact False.elim this
      · intro hf
        have hf1 : f = sipFace1 := by
          simpa using hf
        subst hf1
        exact Finset.mem_filter.2 ⟨h1, by
          simp [ambientFaceBoundary, sharedInteriorPairAnnulusEmbedding,
            sharedInteriorPairFaceBoundary, sipFace1, sip24]⟩
    simp [hfilter]

theorem relativeBoundarySupport_singleton_sipFace2 :
    relativeBoundarySupport
        (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
          sharedInteriorPairAnnulusEmbedding.faceBoundary)
        ({sipFace2} : Finset (AmbientFace sharedInteriorPairAnnulusEmbedding.faces)) =
      {sip56, sip67, sip75} := by
  decide

theorem not_nonempty_planarBoundaryAnnulusWitnessAssignment_sharedInteriorPairCanonicalDecomposition :
    ¬ Nonempty
      (PlanarBoundaryAnnulusWitnessAssignment
        (planarBoundaryAnnulusDecomposition_of_boundaryData sharedInteriorPairBoundaryData)) := by
  exact
    not_nonempty_planarBoundaryAnnulusWitnessAssignment_of_exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusBoundarySource
      sharedInteriorPairClosedWalkAnnulusBoundarySource
      ⟨sipFace0, exists_two_distinct_interior_edges_on_sipFace0_boundary⟩

theorem not_nonempty_planarBoundaryCanonicalWitnessChoice_sharedInteriorPairBoundaryData :
    ¬ Nonempty
      (PlanarBoundaryCanonicalWitnessChoice sharedInteriorPairBoundaryData) := by
  exact
    not_nonempty_planarBoundaryCanonicalWitnessChoice_of_exists_two_distinct_interior_edges_on_faceBoundary_of_closedWalkAnnulusBoundarySource
      sharedInteriorPairClosedWalkAnnulusBoundarySource
      ⟨sipFace0, exists_two_distinct_interior_edges_on_sipFace0_boundary⟩

theorem not_exists_oneCollar_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair :
    ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 1 := by
  exact
    not_exists_planarBoundaryAnnulusCollarGeometry_of_numCollars_eq_one_and_exists_two_distinct_interior_edges_on_faceBoundary
      ⟨sipFace0, exists_two_distinct_interior_edges_on_sipFace0_boundary⟩

theorem sipFace0_not_mem_terminal_collarFaces
    (data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding)
    {i : Fin data.numCollars}
    (hiLast : i.1 + 1 = data.numCollars) :
    sipFace0 ∉ data.collarFaces i := by
  intro hf
  exact
    false_of_mem_terminal_collarFaces_and_exists_two_distinct_interior_edges_on_faceBoundary
      data.toWitnessAssignment hiLast hf
      exists_two_distinct_interior_edges_on_sipFace0_boundary

theorem sipFace1_not_mem_terminal_collarFaces
    (data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding)
    {i : Fin data.numCollars}
    (hiLast : i.1 + 1 = data.numCollars) :
    sipFace1 ∉ data.collarFaces i := by
  intro hf
  exact
    false_of_mem_terminal_collarFaces_and_exists_two_distinct_interior_edges_on_faceBoundary
      data.toWitnessAssignment hiLast hf
      exists_two_distinct_interior_edges_on_sipFace1_boundary

/-- Honest closed-walk annulus source data does not force canonical witness ownership. This model
already has the full source package, but the canonical decomposition extracted from that source
cannot choose a single witness edge on `sipFace0` because two distinct interior edges remain on
the face boundary. -/
theorem
    closedWalkAnnulusBoundarySource_without_canonicalWitnessAssignment_sharedInteriorPair :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData sharedInteriorPairBoundaryData)) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryAnnulusWitnessAssignment_sharedInteriorPairCanonicalDecomposition⟩

/-- The same honest source blocks the newer explicit canonical-witness-choice repair surface
directly. The obstruction is not merely that a derived witness assignment would fail: the required
facewise choice itself cannot exist on the source boundary split. -/
theorem
    closedWalkAnnulusBoundarySource_without_canonicalWitnessChoice_sharedInteriorPair :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryCanonicalWitnessChoice sharedInteriorPairBoundaryData) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryCanonicalWitnessChoice_sharedInteriorPairBoundaryData⟩

/-- In contrast, the weak current-boundary shell is already positively inhabited on the same
source boundary split: the extracted annulus boundary data canonically yields one-collar
current-boundary data without choosing any witness ownership. -/
theorem
    closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData = sharedInteriorPairBoundaryData := by
  refine ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource, ?_⟩
  simpa [sharedInteriorPairBoundaryData] using
    exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
      sharedInteriorPairClosedWalkAnnulusBoundarySource

/-- The same honest source also blocks the whole one-collar weak annulus-geometry route on the
same embedding. The obstruction is no longer tied to the canonical decomposition: any one-collar
collar geometry would still have to place all non-witness edges of `sipFace0` on ambient annulus
boundaries, which is incompatible with its second interior edge. -/
theorem
    closedWalkAnnulusBoundarySource_without_oneCollarAnnulusCollarGeometry_sharedInteriorPair :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding,
          data.numCollars = 1 := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_exists_oneCollar_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

theorem exists_embedding_closedWalkAnnulusBoundarySource_without_canonicalWitnessAssignment_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ Nonempty
          (PlanarBoundaryAnnulusWitnessAssignment
            (planarBoundaryAnnulusDecomposition_of_boundaryData
              source.toPlanarBoundaryAnnulusBoundaryData)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryAnnulusWitnessAssignment_sharedInteriorPairCanonicalDecomposition⟩

theorem exists_embedding_closedWalkAnnulusBoundarySource_without_canonicalWitnessChoice_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryCanonicalWitnessChoice_sharedInteriorPairBoundaryData⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  simpa [sharedInteriorPairBoundaryData] using
    (exists_oneCollarAnnulusCurrentBoundaryData_with_sourceBoundaryData_of_exists_closedWalkAnnulusBoundarySource
      (G := sharedInteriorPairAnnulusGraph)
      ⟨sharedInteriorPairAnnulusEmbedding, nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource⟩)

/-- There is no universal same-embedding derivation from an honest closed-walk annulus source to
the explicit canonical witness-choice repair surface. -/
theorem
    not_forall_exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              source.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun _emb source =>
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData))
      exists_embedding_closedWalkAnnulusBoundarySource_without_canonicalWitnessChoice_sharedInteriorPair

theorem exists_embedding_closedWalkAnnulusBoundarySource_without_oneCollarAnnulusCollarGeometry_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _ : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb, data.numCollars = 1 := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_exists_oneCollar_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

theorem
    not_exists_twoCollar_planarBoundaryAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData :
    ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 2 ∧
          data.toPlanarBoundaryAnnulusBoundaryData = sharedInteriorPairBoundaryData := by
  rintro ⟨data, hnum, hboundary⟩
  let j : Fin data.numCollars := ⟨1, by omega⟩
  have hjpos : 0 < j.1 := by
    dsimp [j]
    omega
  have hnoLater : ∀ k : Fin data.numCollars, ¬ j < k := by
    intro k
    dsimp [j]
    omega
  have hlaterEmpty : laterLayerFaces data.collarFaces j = ∅ := by
    exact laterLayerFaces_eq_empty_of_forall_not_lt data.collarFaces j hnoLater
  have hcurrentEq :
      relativeBoundarySupport
          (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (data.collarFaces j) =
        data.currentBoundary j ∪ data.innerAmbientBoundary := by
    simpa [hlaterEmpty] using data.hcurrentBoundary j
  have hcurrentInterior :
      data.currentBoundary j ⊆
        interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces :=
    data.hcurrentBoundaryInterior j hjpos
  have hcurrentInnerDisjoint := data.hcurrentBoundaryDisjointInner j
  have hcollarNonempty :
      (data.collarFaces j).Nonempty := by
    let decomp := data.toPlanarBoundaryAnnulusDecomposition
    simpa [j, decomp] using decomp.collarFaces_nonempty j
  have hsip23NotInner : sip23 ∉ data.innerAmbientBoundary := by
    intro hsip23Inner
    exact
      sip23_not_mem_sharedInteriorPairInnerAmbientBoundary
        (by simpa [hboundary] using hsip23Inner)
  have hsip24NotInner : sip24 ∉ data.innerAmbientBoundary := by
    intro hsip24Inner
    exact
      sip24_not_mem_sharedInteriorPairInnerAmbientBoundary
        (by simpa [hboundary] using hsip24Inner)
  have hsip56Inner : sip56 ∈ data.innerAmbientBoundary := by
    simpa [hboundary] using sip56_mem_sharedInteriorPairInnerAmbientBoundary
  have hsip67Inner : sip67 ∈ data.innerAmbientBoundary := by
    simpa [hboundary] using sip67_mem_sharedInteriorPairInnerAmbientBoundary
  have hsip75Inner : sip75 ∈ data.innerAmbientBoundary := by
    simpa [hboundary] using sip75_mem_sharedInteriorPairInnerAmbientBoundary
  by_cases h0 : sipFace0 ∈ data.collarFaces j
  · have hsip23Boundary :
        sip23 ∈ relativeBoundarySupport
          (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (data.collarFaces j) :=
      sip23_mem_relativeBoundarySupport_of_sipFace0_mem h0
    have hsip23Union : sip23 ∈ data.currentBoundary j ∪ data.innerAmbientBoundary := by
      rw [← hcurrentEq]
      exact hsip23Boundary
    rcases Finset.mem_union.1 hsip23Union with hsip23Current | hsip23Inner
    · exact
        (Finset.disjoint_left.mp
          (selectedBoundarySupport_disjoint_interiorEdgeSupport
            sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces))
          sip23_mem_selectedBoundarySupport (hcurrentInterior hsip23Current)
    · exact hsip23NotInner hsip23Inner
  · by_cases h1 : sipFace1 ∈ data.collarFaces j
    · have hsip24Boundary :
          sip24 ∈ relativeBoundarySupport
            (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
              sharedInteriorPairAnnulusEmbedding.faceBoundary)
            (data.collarFaces j) :=
        sip24_mem_relativeBoundarySupport_of_sipFace1_mem h1
      have hsip24Union : sip24 ∈ data.currentBoundary j ∪ data.innerAmbientBoundary := by
        rw [← hcurrentEq]
        exact hsip24Boundary
      rcases Finset.mem_union.1 hsip24Union with hsip24Current | hsip24Inner
      · exact
          (Finset.disjoint_left.mp
            (selectedBoundarySupport_disjoint_interiorEdgeSupport
              sharedInteriorPairAnnulusEmbedding.faceBoundary
              sharedInteriorPairAnnulusEmbedding.faces))
            sip24_mem_selectedBoundarySupport (hcurrentInterior hsip24Current)
      · exact hsip24NotInner hsip24Inner
    · have h2 : sipFace2 ∈ data.collarFaces j := by
        rcases hcollarNonempty with ⟨f, hf⟩
        rcases sipFace_cases f with rfl | rfl | rfl
        · exact False.elim (h0 hf)
        · exact False.elim (h1 hf)
        · exact hf
      have hsingleton : data.collarFaces j = {sipFace2} := by
        ext f
        constructor
        · intro hf
          rcases sipFace_cases f with rfl | rfl | rfl
          · exact False.elim (h0 hf)
          · exact False.elim (h1 hf)
          · simp
        · intro hf
          have hf2 : f = sipFace2 := by
            simpa using hf
          subst hf2
          exact h2
      rcases data.hcurrentBoundaryNonempty j with ⟨e, heCurrent⟩
      have heBoundary :
          e ∈ relativeBoundarySupport
            (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
              sharedInteriorPairAnnulusEmbedding.faceBoundary)
            (data.collarFaces j) := by
        rw [hcurrentEq]
        exact Finset.mem_union.2 <| Or.inl heCurrent
      have heFace2 :
          e ∈ ({sip56, sip67, sip75} :
            Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
        simpa [hsingleton, relativeBoundarySupport_singleton_sipFace2] using heBoundary
      have heInner : e ∈ data.innerAmbientBoundary := by
        rcases Finset.mem_insert.1 heFace2 with rfl | heRest
        · exact hsip56Inner
        · rcases Finset.mem_insert.1 heRest with rfl | heLast
          · exact hsip67Inner
          · have : e = sip75 := by simpa using heLast
            subst this
            exact hsip75Inner
      exact (Finset.disjoint_left.mp hcurrentInnerDisjoint) heCurrent heInner

theorem
    closedWalkAnnulusBoundarySource_without_twoCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
          data.numCollars = 2 ∧
            data.toPlanarBoundaryAnnulusBoundaryData = sharedInteriorPairBoundaryData := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_exists_twoCollar_planarBoundaryAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_without_twoCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 2 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_exists_twoCollar_planarBoundaryAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData⟩

theorem
    not_exists_twoCollar_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData :
    ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 2 ∧
          data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
            sharedInteriorPairBoundaryData := by
  rintro ⟨data, hnum, hboundary⟩
  exact
    not_exists_twoCollar_planarBoundaryAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData
      ⟨data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusCurrentBoundaryData, by
          simpa using hnum, by
          simpa using hboundary⟩

theorem
    closedWalkAnnulusBoundarySource_without_twoCollarAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding,
          data.numCollars = 2 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              sharedInteriorPairBoundaryData := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_exists_twoCollar_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_without_twoCollarAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
            data.numCollars = 2 ∧
              data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_exists_twoCollar_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData⟩

theorem
    not_exists_threeCollar_planarBoundaryAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData :
    ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 3 ∧
          data.toPlanarBoundaryAnnulusBoundaryData = sharedInteriorPairBoundaryData := by
  rintro ⟨data, hnum, hboundary⟩
  let jLast : Fin data.numCollars := ⟨2, by omega⟩
  have hjLastPos : 0 < jLast.1 := by
    dsimp [jLast]
    omega
  have hnoLaterLast : ∀ k : Fin data.numCollars, ¬ jLast < k := by
    intro k
    have hklt : k.1 < 3 := by
      simpa [hnum] using k.isLt
    intro hjk
    have hkgt : 2 < k.1 := by
      simpa [jLast] using hjk
    omega
  have hlaterLastEmpty : laterLayerFaces data.collarFaces jLast = ∅ := by
    exact laterLayerFaces_eq_empty_of_forall_not_lt data.collarFaces jLast hnoLaterLast
  have hcurrentEqLast :
      relativeBoundarySupport
          (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (data.collarFaces jLast) =
        data.currentBoundary jLast ∪ data.innerAmbientBoundary := by
    simpa [hlaterLastEmpty] using data.hcurrentBoundary jLast
  have hcurrentLastInterior :
      data.currentBoundary jLast ⊆
        interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces :=
    data.hcurrentBoundaryInterior jLast hjLastPos
  have hlastNonempty :
      (data.collarFaces jLast).Nonempty := by
    let decomp := data.toPlanarBoundaryAnnulusDecomposition
    simpa [jLast, decomp] using decomp.collarFaces_nonempty jLast
  have hsip23NotInner : sip23 ∉ data.innerAmbientBoundary := by
    intro hsip23Inner
    exact
      sip23_not_mem_sharedInteriorPairInnerAmbientBoundary
        (by simpa [hboundary] using hsip23Inner)
  have hsip24NotInner : sip24 ∉ data.innerAmbientBoundary := by
    intro hsip24Inner
    exact
      sip24_not_mem_sharedInteriorPairInnerAmbientBoundary
        (by simpa [hboundary] using hsip24Inner)
  have hlast0 : sipFace0 ∉ data.collarFaces jLast := by
    intro h0
    have hsip23Boundary :
        sip23 ∈ relativeBoundarySupport
          (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (data.collarFaces jLast) :=
      sip23_mem_relativeBoundarySupport_of_sipFace0_mem h0
    have hsip23Union : sip23 ∈ data.currentBoundary jLast ∪ data.innerAmbientBoundary := by
      rw [← hcurrentEqLast]
      exact hsip23Boundary
    rcases Finset.mem_union.1 hsip23Union with hsip23Current | hsip23Inner
    · exact
        (Finset.disjoint_left.mp
          (selectedBoundarySupport_disjoint_interiorEdgeSupport
            sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces))
          sip23_mem_selectedBoundarySupport (hcurrentLastInterior hsip23Current)
    · exact hsip23NotInner hsip23Inner
  have hlast1 : sipFace1 ∉ data.collarFaces jLast := by
    intro h1
    have hsip24Boundary :
        sip24 ∈ relativeBoundarySupport
          (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (data.collarFaces jLast) :=
      sip24_mem_relativeBoundarySupport_of_sipFace1_mem h1
    have hsip24Union : sip24 ∈ data.currentBoundary jLast ∪ data.innerAmbientBoundary := by
      rw [← hcurrentEqLast]
      exact hsip24Boundary
    rcases Finset.mem_union.1 hsip24Union with hsip24Current | hsip24Inner
    · exact
        (Finset.disjoint_left.mp
          (selectedBoundarySupport_disjoint_interiorEdgeSupport
            sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces))
          sip24_mem_selectedBoundarySupport (hcurrentLastInterior hsip24Current)
    · exact hsip24NotInner hsip24Inner
  have hlast2 : sipFace2 ∈ data.collarFaces jLast := by
    rcases hlastNonempty with ⟨f, hf⟩
    rcases sipFace_cases f with rfl | rfl | rfl
    · exact False.elim (hlast0 hf)
    · exact False.elim (hlast1 hf)
    · exact hf
  let jMid : Fin data.numCollars := ⟨1, by omega⟩
  have hjMidPos : 0 < jMid.1 := by
    dsimp [jMid]
    omega
  have hjMidSucc : jMid.1 + 1 < data.numCollars := by
    dsimp [jMid]
    omega
  have hnextMid : (⟨jMid.1 + 1, hjMidSucc⟩ : Fin data.numCollars) = jLast := by
    apply Fin.ext
    dsimp [jMid, jLast]
  have hlaterMid :
      laterLayerFaces data.collarFaces jMid = data.collarFaces jLast := by
    calc
      laterLayerFaces data.collarFaces jMid =
          data.collarFaces ⟨jMid.1 + 1, hjMidSucc⟩ ∪
            laterLayerFaces data.collarFaces ⟨jMid.1 + 1, hjMidSucc⟩ := by
            simpa using
              laterLayerFaces_eq_collarFaces_union_laterLayerFaces_next
                data.collarFaces jMid hjMidSucc
      _ = data.collarFaces jLast ∪ laterLayerFaces data.collarFaces jLast := by
            simp [hnextMid]
      _ = data.collarFaces jLast := by simp [hlaterLastEmpty]
  have hcurrentEqMid :
      relativeBoundarySupport
          (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (data.collarFaces jMid ∪ data.collarFaces jLast) =
        data.currentBoundary jMid ∪ data.innerAmbientBoundary := by
    simpa [hlaterMid] using data.hcurrentBoundary jMid
  have hcurrentMidInterior :
      data.currentBoundary jMid ⊆
        interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces :=
    data.hcurrentBoundaryInterior jMid hjMidPos
  have hmidNonempty :
      (data.collarFaces jMid).Nonempty := by
    let decomp := data.toPlanarBoundaryAnnulusDecomposition
    simpa [jMid, decomp] using decomp.collarFaces_nonempty jMid
  have hjMidNeLast : jMid ≠ jLast := by
    intro h
    have hval := congrArg (fun x : Fin data.numCollars => x.1) h
    dsimp [jMid, jLast] at hval
    omega
  have hdisjointMidLast :
      Disjoint (data.collarFaces jMid) (data.collarFaces jLast) :=
    data.hdisjoint (i := jMid) (j := jLast) hjMidNeLast
  have hmid2 : sipFace2 ∉ data.collarFaces jMid := by
    intro hmid2
    exact
      (Finset.disjoint_left.mp hdisjointMidLast) hmid2 hlast2
  rcases hmidNonempty with ⟨f, hf⟩
  rcases sipFace_cases f with rfl | rfl | rfl
  · have hsip23Boundary :
        sip23 ∈ relativeBoundarySupport
          (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (data.collarFaces jMid ∪ data.collarFaces jLast) :=
      sip23_mem_relativeBoundarySupport_of_sipFace0_mem (Finset.mem_union.2 <| Or.inl hf)
    have hsip23Union : sip23 ∈ data.currentBoundary jMid ∪ data.innerAmbientBoundary := by
      rw [← hcurrentEqMid]
      exact hsip23Boundary
    rcases Finset.mem_union.1 hsip23Union with hsip23Current | hsip23Inner
    · exact
        (Finset.disjoint_left.mp
          (selectedBoundarySupport_disjoint_interiorEdgeSupport
            sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces))
          sip23_mem_selectedBoundarySupport (hcurrentMidInterior hsip23Current)
    · exact hsip23NotInner hsip23Inner
  · have hsip24Boundary :
        sip24 ∈ relativeBoundarySupport
          (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (data.collarFaces jMid ∪ data.collarFaces jLast) :=
      sip24_mem_relativeBoundarySupport_of_sipFace1_mem (Finset.mem_union.2 <| Or.inl hf)
    have hsip24Union : sip24 ∈ data.currentBoundary jMid ∪ data.innerAmbientBoundary := by
      rw [← hcurrentEqMid]
      exact hsip24Boundary
    rcases Finset.mem_union.1 hsip24Union with hsip24Current | hsip24Inner
    · exact
        (Finset.disjoint_left.mp
          (selectedBoundarySupport_disjoint_interiorEdgeSupport
            sharedInteriorPairAnnulusEmbedding.faceBoundary
            sharedInteriorPairAnnulusEmbedding.faces))
          sip24_mem_selectedBoundarySupport (hcurrentMidInterior hsip24Current)
    · exact hsip24NotInner hsip24Inner
  · exact False.elim (hmid2 hf)

theorem
    closedWalkAnnulusBoundarySource_without_threeCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
          data.numCollars = 3 ∧
            data.toPlanarBoundaryAnnulusBoundaryData = sharedInteriorPairBoundaryData := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_exists_threeCollar_planarBoundaryAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_without_threeCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 3 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_exists_threeCollar_planarBoundaryAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData⟩

theorem
    not_exists_threeCollar_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData :
    ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 3 ∧
          data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
            sharedInteriorPairBoundaryData := by
  exact
    not_exists_planarBoundaryAnnulusCollarGeometry_of_not_exists_planarBoundaryAnnulusCurrentBoundaryData_of_numCollars_eq_and_boundaryData
      not_exists_threeCollar_planarBoundaryAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData

theorem
    closedWalkAnnulusBoundarySource_without_threeCollarAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding,
          data.numCollars = 3 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              sharedInteriorPairBoundaryData := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_exists_threeCollar_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_without_threeCollarAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
            data.numCollars = 3 ∧
              data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_exists_threeCollar_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData⟩

theorem card_ambientFace_sharedInteriorPairAnnulusEmbedding :
    Fintype.card (AmbientFace sharedInteriorPairAnnulusEmbedding.faces) = 3 := by
  simp [AmbientFace, sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaces]

theorem
    numCollars_le_three_of_planarBoundaryAnnulusCurrentBoundaryData_sharedInteriorPair
    (data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding) :
    data.numCollars ≤ 3 := by
  have hle := data.numCollars_le_card_faces
  simpa [card_ambientFace_sharedInteriorPairAnnulusEmbedding] using hle

theorem
    numCollars_le_three_of_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair
    (data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding) :
    data.numCollars ≤ 3 := by
  have hle := data.numCollars_le_card_faces
  simpa [card_ambientFace_sharedInteriorPairAnnulusEmbedding] using hle

theorem terminal_collarFaces_eq_singleton_sipFace2
    (data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding)
    {i : Fin data.numCollars}
    (hiLast : i.1 + 1 = data.numCollars)
    (hnonempty : (data.collarFaces i).Nonempty) :
    data.collarFaces i = {sipFace2} := by
  have hnot0 := sipFace0_not_mem_terminal_collarFaces data hiLast
  have hnot1 := sipFace1_not_mem_terminal_collarFaces data hiLast
  have h2 : sipFace2 ∈ data.collarFaces i := by
    rcases hnonempty with ⟨f, hf⟩
    rcases sipFace_cases f with rfl | rfl | rfl
    · exact False.elim (hnot0 hf)
    · exact False.elim (hnot1 hf)
    · exact hf
  ext f
  constructor
  · intro hf
    rcases sipFace_cases f with rfl | rfl | rfl
    · exact False.elim (hnot0 hf)
    · exact False.elim (hnot1 hf)
    · simp
  · intro hf
    have hf2 : f = sipFace2 := by
      simpa using hf
    subst hf2
    exact h2

theorem
    false_of_intermediateBoundary_before_singleton_sipFace2
    (data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding)
    {i : Fin data.numCollars}
    (hi : i.1 + 1 < data.numCollars)
    (hrem : data.remainderFaces i = {sipFace2}) :
    False := by
  rcases data.hintermediateBoundaryNonempty i hi with ⟨e, he⟩
  have heInterior :
      e ∈ interiorEdgeSupport sharedInteriorPairAnnulusEmbedding.faceBoundary
        sharedInteriorPairAnnulusEmbedding.faces :=
    data.hintermediateBoundaryInterior i hi he
  have heRel :
      e ∈ relativeBoundarySupport
        (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
          sharedInteriorPairAnnulusEmbedding.faceBoundary)
        ({sipFace2} : Finset (AmbientFace sharedInteriorPairAnnulusEmbedding.faces)) := by
    have hsubset := data.hinnerBoundary i hi he
    simpa [hrem] using hsubset
  have heFace2 :
      e ∈ ({sip56, sip67, sip75} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
    simpa [relativeBoundarySupport_singleton_sipFace2] using heRel
  have heSelected :
      e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
        sharedInteriorPairAnnulusEmbedding.faces sharedInteriorPairAnnulusEmbedding.faces := by
    rcases Finset.mem_insert.1 heFace2 with rfl | heRest
    · exact sip56_mem_selectedBoundarySupport
    · rcases Finset.mem_insert.1 heRest with rfl | heLast
      · exact sip67_mem_selectedBoundarySupport
      · have : e = sip75 := by simpa using heLast
        subst this
        exact sip75_mem_selectedBoundarySupport
  exact
    (Finset.disjoint_left.mp
      (selectedBoundarySupport_disjoint_interiorEdgeSupport
        sharedInteriorPairAnnulusEmbedding.faceBoundary
        sharedInteriorPairAnnulusEmbedding.faces))
      heSelected heInterior

theorem
    not_exists_twoCollar_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair :
    ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 2 := by
  rintro ⟨data, hnum⟩
  let i : Fin data.numCollars := ⟨0, by omega⟩
  let jLast : Fin data.numCollars := ⟨1, by omega⟩
  have hi : i.1 + 1 < data.numCollars := by
    dsimp [i]
    omega
  have hjLast : jLast.1 + 1 = data.numCollars := by
    dsimp [jLast]
    omega
  have hnoLaterLast : ∀ k : Fin data.numCollars, ¬ jLast < k := by
    intro k
    have hklt : k.1 < 2 := by
      simpa [hnum] using k.isLt
    intro hjk
    have hkgt : 1 < k.1 := by
      simpa [jLast] using hjk
    omega
  have hlaterLastEmpty : laterLayerFaces data.collarFaces jLast = ∅ := by
    exact laterLayerFaces_eq_empty_of_forall_not_lt data.collarFaces jLast hnoLaterLast
  have hnext : (⟨i.1 + 1, hi⟩ : Fin data.numCollars) = jLast := by
    apply Fin.ext
    dsimp [i, jLast]
  have hlater :
      laterLayerFaces data.collarFaces i = data.collarFaces jLast := by
    calc
      laterLayerFaces data.collarFaces i =
          data.collarFaces ⟨i.1 + 1, hi⟩ ∪
            laterLayerFaces data.collarFaces ⟨i.1 + 1, hi⟩ := by
            simpa using
              laterLayerFaces_eq_collarFaces_union_laterLayerFaces_next
                data.collarFaces i hi
      _ = data.collarFaces jLast ∪ laterLayerFaces data.collarFaces jLast := by
            simp [hnext]
      _ = data.collarFaces jLast := by
            simp [hlaterLastEmpty]
  have hlastNonempty :
      (data.collarFaces jLast).Nonempty := by
    let decomp := data.toPlanarBoundaryAnnulusDecomposition
    simpa [jLast, decomp] using decomp.collarFaces_nonempty jLast
  have hlastSingleton :
      data.collarFaces jLast = {sipFace2} :=
    terminal_collarFaces_eq_singleton_sipFace2 data hjLast hlastNonempty
  have hrem : data.remainderFaces i = {sipFace2} := by
    calc
      data.remainderFaces i = laterLayerFaces data.collarFaces i := data.hremainder i
      _ = data.collarFaces jLast := hlater
      _ = {sipFace2} := hlastSingleton
  exact false_of_intermediateBoundary_before_singleton_sipFace2 data hi hrem

theorem
    not_exists_threeCollar_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair :
    ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 3 := by
  rintro ⟨data, hnum⟩
  let jMid : Fin data.numCollars := ⟨1, by omega⟩
  let jLast : Fin data.numCollars := ⟨2, by omega⟩
  have hjMid : jMid.1 + 1 < data.numCollars := by
    dsimp [jMid]
    omega
  have hjLast : jLast.1 + 1 = data.numCollars := by
    dsimp [jLast]
    omega
  have hnoLaterLast : ∀ k : Fin data.numCollars, ¬ jLast < k := by
    intro k
    have hklt : k.1 < 3 := by
      simpa [hnum] using k.isLt
    intro hjk
    have hkgt : 2 < k.1 := by
      simpa [jLast] using hjk
    omega
  have hlaterLastEmpty : laterLayerFaces data.collarFaces jLast = ∅ := by
    exact laterLayerFaces_eq_empty_of_forall_not_lt data.collarFaces jLast hnoLaterLast
  have hnext : (⟨jMid.1 + 1, hjMid⟩ : Fin data.numCollars) = jLast := by
    apply Fin.ext
    dsimp [jMid, jLast]
  have hlater :
      laterLayerFaces data.collarFaces jMid = data.collarFaces jLast := by
    calc
      laterLayerFaces data.collarFaces jMid =
          data.collarFaces ⟨jMid.1 + 1, hjMid⟩ ∪
            laterLayerFaces data.collarFaces ⟨jMid.1 + 1, hjMid⟩ := by
            simpa using
              laterLayerFaces_eq_collarFaces_union_laterLayerFaces_next
                data.collarFaces jMid hjMid
      _ = data.collarFaces jLast ∪ laterLayerFaces data.collarFaces jLast := by
            simp [hnext]
      _ = data.collarFaces jLast := by
            simp [hlaterLastEmpty]
  have hlastNonempty :
      (data.collarFaces jLast).Nonempty := by
    let decomp := data.toPlanarBoundaryAnnulusDecomposition
    simpa [jLast, decomp] using decomp.collarFaces_nonempty jLast
  have hlastSingleton :
      data.collarFaces jLast = {sipFace2} :=
    terminal_collarFaces_eq_singleton_sipFace2 data hjLast hlastNonempty
  have hrem : data.remainderFaces jMid = {sipFace2} := by
    calc
      data.remainderFaces jMid = laterLayerFaces data.collarFaces jMid := data.hremainder jMid
      _ = data.collarFaces jLast := hlater
      _ = {sipFace2} := hlastSingleton
  exact false_of_intermediateBoundary_before_singleton_sipFace2 data hjMid hrem

theorem
    not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair :
    ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding) := by
  rintro ⟨data⟩
  have hpos : 0 < data.numCollars := data.toPlanarBoundaryAnnulusDecomposition.numCollars_pos
  have hle : data.numCollars ≤ 3 :=
    numCollars_le_three_of_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair data
  have hcases : data.numCollars = 1 ∨ data.numCollars = 2 ∨ data.numCollars = 3 := by
    omega
  rcases hcases with h1 | h2 | h3
  · exact not_exists_oneCollar_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair ⟨data, h1⟩
  · exact not_exists_twoCollar_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair ⟨data, h2⟩
  · exact not_exists_threeCollar_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair ⟨data, h3⟩

/-- The shared-interior-pair honest source also blocks the repaired previous-boundary witness
surface: that surface extends weak collar geometry, and this embedding has no weak collar
geometry at all. -/
theorem
    not_nonempty_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_sharedInteriorPair :
    ¬ Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          sharedInteriorPairAnnulusEmbedding) := by
  rintro ⟨data⟩
  exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair
    ⟨data.toPlanarBoundaryAnnulusCollarGeometry⟩

theorem
    closedWalkAnnulusBoundarySource_without_annulusCollarGeometry_sharedInteriorPair :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_without_annulusCollarGeometry_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

/-- Honest closed-walk annulus source data alone does not force the repaired
previous-boundary witness surface. -/
theorem
    closedWalkAnnulusBoundarySource_without_previousBoundaryWitness_sharedInteriorPair :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_sharedInteriorPair⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_without_previousBoundaryWitness_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_sharedInteriorPair⟩

/-- There is no universal same-embedding theorem from an honest source alone to the repaired
previous-boundary witness surface. -/
theorem
    not_forall_exists_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_of_closedWalkAnnulusBoundarySource_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) := by
  intro h
  exact
    not_nonempty_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding sharedInteriorPairClosedWalkAnnulusBoundarySource)

theorem
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_of_closedWalkAnnulusBoundarySource_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  exact
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_of_exists_embedding_closedWalkAnnulusBoundarySource_without_annulusCollarGeometry
      exists_embedding_closedWalkAnnulusBoundarySource_without_annulusCollarGeometry_sharedInteriorPair

/-- The same two shared interior edges also block the weaker height-ordered witness-cover surface.
Covering `sip01` forces some peeled outer face to choose it.  The other shared interior edge
`sip12` then has to be chosen by a strictly later peeled face.  Repeating the argument from that
later `sip12` face forces a still-later `sip01` face, but there are only the two outer faces that
can choose either shared edge. -/
theorem
    not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair :
    ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          sharedInteriorPairAnnulusEmbedding) := by
  rintro ⟨data⟩
  rcases Finset.mem_image.1 (data.hcover sip01_mem_interiorEdgeSupport) with
    ⟨f01, hf01Peel, hf01Witness⟩
  have hf01WitnessMem :
      data.witnessEdge f01 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f01.1 :=
    data.hwitness f01 hf01Peel
  have hsip01_f01 :
      sip01 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f01.1 := by
    simpa [hf01Witness] using hf01WitnessMem
  have hsip12_f01 :
      sip12 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f01.1 :=
    sip12_mem_faceBoundary_of_sip01_mem hsip01_f01
  have hsip12_erase :
      sip12 ∈
        (sharedInteriorPairAnnulusEmbedding.faceBoundary f01.1).erase
          (data.witnessEdge f01) := by
    refine Finset.mem_erase.2 ⟨?_, hsip12_f01⟩
    intro h
    exact sip01_ne_sip12 (hf01Witness.symm.trans h.symm)
  rcases data.hrest f01 hf01Peel sip12 hsip12_erase with
    hsip12Boundary | ⟨f12, hf12Peel, hf12Witness, hlt01_12⟩
  · exact sip12_not_mem_selectedBoundarySupport hsip12Boundary
  have hf12WitnessMem :
      data.witnessEdge f12 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f12.1 :=
    data.hwitness f12 hf12Peel
  have hsip12_f12 :
      sip12 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f12.1 := by
    simpa [hf12Witness] using hf12WitnessMem
  have hsip01_f12 :
      sip01 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f12.1 :=
    sip01_mem_faceBoundary_of_sip12_mem hsip12_f12
  have hsip01_erase :
      sip01 ∈
        (sharedInteriorPairAnnulusEmbedding.faceBoundary f12.1).erase
          (data.witnessEdge f12) := by
    refine Finset.mem_erase.2 ⟨?_, hsip01_f12⟩
    intro h
    exact sip01_ne_sip12 (h.trans hf12Witness)
  rcases data.hrest f12 hf12Peel sip01 hsip01_erase with
    hsip01Boundary | ⟨f01Next, hf01NextPeel, hf01NextWitness, hlt12_next⟩
  · exact sip01_not_mem_selectedBoundarySupport hsip01Boundary
  have hf01NextWitnessMem :
      data.witnessEdge f01Next ∈
        sharedInteriorPairAnnulusEmbedding.faceBoundary f01Next.1 :=
    data.hwitness f01Next hf01NextPeel
  have hsip01_f01Next :
      sip01 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f01Next.1 := by
    simpa [hf01NextWitness] using hf01NextWitnessMem
  have hf01_cases : f01 = sipFace0 ∨ f01 = sipFace1 :=
    (sip01_mem_faceBoundary_iff f01).1 hsip01_f01
  have hf12_cases : f12 = sipFace0 ∨ f12 = sipFace1 :=
    (sip12_mem_faceBoundary_iff f12).1 hsip12_f12
  have hf01Next_cases : f01Next = sipFace0 ∨ f01Next = sipFace1 :=
    (sip01_mem_faceBoundary_iff f01Next).1 hsip01_f01Next
  have hf01_ne_f12 : f01 ≠ f12 := by
    intro h
    subst h
    exact sip01_ne_sip12 (hf01Witness.symm.trans hf12Witness)
  have hf01Next_ne_f12 : f01Next ≠ f12 := by
    intro h
    subst h
    exact sip01_ne_sip12 (hf01NextWitness.symm.trans hf12Witness)
  have hf01Next_eq_f01 : f01Next = f01 := by
    rcases hf01_cases with rfl | rfl
    · rcases hf12_cases with rfl | rfl
      · exact False.elim (hf01_ne_f12 rfl)
      · rcases hf01Next_cases with rfl | rfl
        · rfl
        · exact False.elim (hf01Next_ne_f12 rfl)
    · rcases hf12_cases with rfl | rfl
      · rcases hf01Next_cases with rfl | rfl
        · exact False.elim (hf01Next_ne_f12 rfl)
        · rfl
      · exact False.elim (hf01_ne_f12 rfl)
  have hlt01_next : data.height f01 < data.height f01Next :=
    lt_trans hlt01_12 hlt12_next
  rw [hf01Next_eq_f01] at hlt01_next
  exact (Nat.lt_irrefl _ hlt01_next).elim

/-- Consequently the finite collar-layer witness-cover repair is impossible on the same source
model as well, since it canonically lowers to the height-ordered witness-cover surface. -/
theorem
    not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair :
    ¬ Nonempty
        (PlanarBoundaryCollarLayerFacePeelWitnessData
          sharedInteriorPairAnnulusEmbedding) := by
  rintro ⟨data⟩
  exact
    not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair
      ⟨data.toHeightOrderedFacePeelWitnessData⟩

/-- The obstruction also reaches the raw attached-face certificate surface consumed directly by
the boundary-aware synthesis theorem.  The proof uses only the finite prefix condition of
`BoundaryRootedFacePeelCertificate`: any occurrence whose witness is `sip01` needs an earlier
`sip12` witness, and conversely any `sip12` witness needs an earlier `sip01` witness.  The generic
prefix-cycle lemma rules this out even if the face order repeats faces. -/
theorem
    not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair :
    ¬ Nonempty
        (BoundaryRootedFacePeelCertificate
          sharedInteriorPairAnnulusEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairAnnulusEmbedding.faceBoundary)) := by
  rintro ⟨cert⟩
  let subBoundary : AmbientFace sharedInteriorPairAnnulusEmbedding.faces →
      Finset sharedInteriorPairAnnulusGraph.edgeSet :=
    ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
      sharedInteriorPairAnnulusEmbedding.faceBoundary
  let base : Finset sharedInteriorPairAnnulusGraph.edgeSet :=
    selectedBoundarySupport subBoundary
      sharedInteriorPairAnnulusEmbedding.faces.attach
      sharedInteriorPairAnnulusEmbedding.faces.attach
  have hbase01 : sip01 ∉ base := by
    intro h
    exact sip01_not_mem_selectedBoundarySupport (by
      simpa [base, subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq
        (faceBoundary := sharedInteriorPairAnnulusEmbedding.faceBoundary)
        (allFaces := sharedInteriorPairAnnulusEmbedding.faces)] using h)
  have hbase12 : sip12 ∉ base := by
    intro h
    exact sip12_not_mem_selectedBoundarySupport (by
      simpa [base, subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq
        (faceBoundary := sharedInteriorPairAnnulusEmbedding.faceBoundary)
        (allFaces := sharedInteriorPairAnnulusEmbedding.faces)] using h)
  have hstep01 :
      ∀ l₁ l₂ f, cert.faceOrder = l₁ ++ f :: l₂ →
        cert.witnessEdge f = sip01 →
          sip12 ∈ base ∪ facePeelWitnessSupport l₁ cert.witnessEdge := by
    intro l₁ l₂ f hsplit hw
    rcases cert.step l₁ l₂ f hsplit with ⟨hwit, hrest⟩
    have hsip01_f :
        sip01 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f.1 := by
      simpa [subBoundary, ambientFaceBoundary, hw] using hwit
    have hsip12_f :
        sip12 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f.1 :=
      sip12_mem_faceBoundary_of_sip01_mem hsip01_f
    have hsip12_sub : sip12 ∈ subBoundary f := by
      simpa [subBoundary, ambientFaceBoundary] using hsip12_f
    have hsip12_erase :
        sip12 ∈ (subBoundary f).erase (cert.witnessEdge f) := by
      refine Finset.mem_erase.2 ⟨?_, hsip12_sub⟩
      intro h
      exact sip01_ne_sip12 (hw.symm.trans h.symm)
    exact hrest hsip12_erase
  have hstep12 :
      ∀ l₁ l₂ f, cert.faceOrder = l₁ ++ f :: l₂ →
        cert.witnessEdge f = sip12 →
          sip01 ∈ base ∪ facePeelWitnessSupport l₁ cert.witnessEdge := by
    intro l₁ l₂ f hsplit hw
    rcases cert.step l₁ l₂ f hsplit with ⟨hwit, hrest⟩
    have hsip12_f :
        sip12 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f.1 := by
      simpa [subBoundary, ambientFaceBoundary, hw] using hwit
    have hsip01_f :
        sip01 ∈ sharedInteriorPairAnnulusEmbedding.faceBoundary f.1 :=
      sip01_mem_faceBoundary_of_sip12_mem hsip12_f
    have hsip01_sub : sip01 ∈ subBoundary f := by
      simpa [subBoundary, ambientFaceBoundary] using hsip01_f
    have hsip01_erase :
        sip01 ∈ (subBoundary f).erase (cert.witnessEdge f) := by
      refine Finset.mem_erase.2 ⟨?_, hsip01_sub⟩
      intro h
      exact sip01_ne_sip12 (h.trans hw)
    exact hrest hsip01_erase
  have hnoPair :
      sip01 ∉ facePeelWitnessSupport cert.faceOrder cert.witnessEdge ∧
        sip12 ∉ facePeelWitnessSupport cert.faceOrder cert.witnessEdge :=
    not_mem_facePeelWitnessSupport_pair_of_twoWitnessPrefixCycle
      (base := base) (witnessEdge := cert.witnessEdge)
      (e₁ := sip01) (e₂ := sip12)
      hbase01 hbase12 cert.faceOrder hstep01 hstep12
  have hsip01Interior :
      sip01 ∈ interiorEdgeSupport subBoundary
        sharedInteriorPairAnnulusEmbedding.faces.attach := by
    simpa [subBoundary, interiorEdgeSupport_ambientFaceBoundary_eq
      (faceBoundary := sharedInteriorPairAnnulusEmbedding.faceBoundary)
      (allFaces := sharedInteriorPairAnnulusEmbedding.faces)] using
        sip01_mem_interiorEdgeSupport
  exact hnoPair.1 (cert.coverInterior hsip01Interior)

/-- Hence the still more structured well-founded-parent witness-cover repair is impossible on
this source as well, since it canonically lowers to the attached-face certificate. -/
theorem
    not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair :
    ¬ Nonempty
        (PlanarBoundaryWellFoundedFacePeelWitnessData
          sharedInteriorPairAnnulusEmbedding) := by
  rintro ⟨data⟩
  exact
    not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair
      ⟨data.toBoundaryRootedFacePeelCertificate⟩

/-- The same-embedding attached-certificate obstruction should not be misread as a graph-level
nonadmissibility theorem for the current boundary-aware certificate package.  The package is
inhabited by the degenerate all-boundary embedding, whose boundary support is every edge and whose
interior support is empty. -/
theorem
    sharedInteriorPairAnnulusGraph_admitsPlanarBoundaryAttachedRootedFacePeelCertificate_via_allBoundaryEmbedding :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate
      sharedInteriorPairAnnulusGraph := by
  letI : Fintype sharedInteriorPairAnnulusGraph.edgeSet := Fintype.ofFinite _
  letI : Inhabited sharedInteriorPairAnnulusGraph.edgeSet := ⟨sip01⟩
  exact
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_fintype_edgeSet
      sharedInteriorPairAnnulusGraph

theorem
    closedWalkAnnulusBoundarySource_without_heightOrderedFacePeelWitnessData_sharedInteriorPair :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryHeightOrderedFacePeelWitnessData
          sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair⟩

theorem
    closedWalkAnnulusBoundarySource_without_collarLayerFacePeelWitnessData_sharedInteriorPair :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryCollarLayerFacePeelWitnessData
          sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair⟩

theorem
    closedWalkAnnulusBoundarySource_without_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty
        (BoundaryRootedFacePeelCertificate
          sharedInteriorPairAnnulusEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairAnnulusEmbedding.faceBoundary)) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair⟩

theorem
    closedWalkAnnulusBoundarySource_and_taitEdgeColoring_without_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
        IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
      ¬ Nonempty
        (BoundaryRootedFacePeelCertificate
          sharedInteriorPairAnnulusEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := sharedInteriorPairAnnulusEmbedding.faces)
            sharedInteriorPairAnnulusEmbedding.faceBoundary)) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair⟩

theorem
    closedWalkAnnulusBoundarySource_without_wellFoundedFacePeelWitnessData_sharedInteriorPair :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ Nonempty
        (PlanarBoundaryWellFoundedFacePeelWitnessData
          sharedInteriorPairAnnulusEmbedding) := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_without_heightOrderedFacePeelWitnessData_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_without_collarLayerFacePeelWitnessData_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_without_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ Nonempty
          (BoundaryRootedFacePeelCertificate emb.faces.attach
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_taitEdgeColoring_without_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
          IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
        ¬ Nonempty
          (BoundaryRootedFacePeelCertificate emb.faces.attach
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_without_wellFoundedFacePeelWitnessData_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair⟩

theorem
    not_forall_exists_planarBoundaryHeightOrderedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) := by
  exact
    not_forall_exists_planarBoundaryHeightOrderedFacePeelWitnessData_of_exists_embedding_closedWalkAnnulusBoundarySource_without_heightOrderedFacePeelWitnessData
      exists_embedding_closedWalkAnnulusBoundarySource_without_heightOrderedFacePeelWitnessData_sharedInteriorPair

theorem
    not_forall_exists_planarBoundaryCollarLayerFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  exact
    not_forall_exists_planarBoundaryCollarLayerFacePeelWitnessData_of_exists_embedding_closedWalkAnnulusBoundarySource_without_collarLayerFacePeelWitnessData
      exists_embedding_closedWalkAnnulusBoundarySource_without_collarLayerFacePeelWitnessData_sharedInteriorPair

theorem
    not_forall_exists_attachedBoundaryRootedFacePeelCertificate_of_closedWalkAnnulusBoundarySource_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) := by
  exact
    not_forall_exists_attachedBoundaryRootedFacePeelCertificate_of_exists_embedding_closedWalkAnnulusBoundarySource_without_attachedBoundaryRootedFacePeelCertificate
      exists_embedding_closedWalkAnnulusBoundarySource_without_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ¬ Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair⟩

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_without_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          ¬ Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair⟩

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_heightOrderedFacePeelWitnessData_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair⟩

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_collarLayerFacePeelWitnessData_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair⟩

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_wellFoundedFacePeelWitnessData_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair⟩

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_annulusCollarGeometry_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_without_currentSufficientSameEmbeddingGeometry_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
          ¬ Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_without_currentSufficientSameEmbeddingGeometry_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
          ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
          ¬ Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

theorem
    not_forall_exists_attachedBoundaryRootedFacePeelCertificate_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) := by
  exact
    not_forall_exists_attachedBoundaryRootedFacePeelCertificate_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_attachedBoundaryRootedFacePeelCertificate
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair

theorem
    not_forall_exists_attachedBoundaryRootedFacePeelCertificate_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) := by
  intro h
  exact
    not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair
      (h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
        exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph)

theorem
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
  rcases hAny with hHeight | hCollar | hAttached | hWellFounded | hAnnulus
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar
  · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair hAttached
  · exact not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair hWellFounded
  · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair hAnnulus

theorem
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
            Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair
  rcases hAny with hHeight | hCollar | hAttached | hWellFounded | hAnnulus
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar
  · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair hAttached
  · exact not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair hWellFounded
  · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair hAnnulus

theorem
    not_forall_exists_planarBoundaryHeightOrderedFacePeelWitnessData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) := by
  exact
    not_forall_exists_planarBoundaryHeightOrderedFacePeelWitnessData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_heightOrderedFacePeelWitnessData
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_heightOrderedFacePeelWitnessData_sharedInteriorPair

theorem
    not_forall_exists_planarBoundaryCollarLayerFacePeelWitnessData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  exact
    not_forall_exists_planarBoundaryCollarLayerFacePeelWitnessData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_collarLayerFacePeelWitnessData
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_collarLayerFacePeelWitnessData_sharedInteriorPair

theorem
    not_forall_exists_planarBoundaryWellFoundedFacePeelWitnessData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) := by
  exact
    not_forall_exists_planarBoundaryWellFoundedFacePeelWitnessData_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_wellFoundedFacePeelWitnessData
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_wellFoundedFacePeelWitnessData_sharedInteriorPair

theorem
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  exact
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_annulusCollarGeometry
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_annulusCollarGeometry_sharedInteriorPair

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    exists_oneCollarAnnulusCurrentBoundaryData_with_sourceBoundaryData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc
      (G := sharedInteriorPairAnnulusGraph)
      ⟨sharedInteriorPairAnnulusEmbedding,
        sharedInteriorPairAnnulusBoundaryReachabilityData,
        sharedInteriorPairDartSuccessorCycleGeometry,
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_without_currentSufficientSameEmbeddingGeometry_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
          ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
          ¬ Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_without_currentSufficientSameEmbeddingGeometry_sharedInteriorPair :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                boundaryData.toPlanarBoundaryAnnulusBoundaryData) ∧
          (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
            IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) ∧
          (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
          ¬ Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
          ¬ Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ¬ Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
          ¬ Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            sharedInteriorPairAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
    let source : PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding :=
      PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        sharedInteriorPairAnnulusBoundaryReachabilityData
        sharedInteriorPairDartSuccessorCycleGeometry
        sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
    rcases exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
      ⟨data, hnum, hboundary⟩
    exact ⟨data, hnum, by
      simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
        PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData] using
        hboundary⟩
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      hcurrent,
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph,
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair,
      not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair,
      not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair,
      not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair⟩

theorem
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 1 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
            Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding sharedInteriorPairClosedWalkAnnulusBoundarySource
      (exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource
        sharedInteriorPairClosedWalkAnnulusBoundarySource)
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair
  rcases hAny with hHeight | hCollar | hAttached | hWellFounded | hAnnulus
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar
  · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair hAttached
  · exact not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair hWellFounded
  · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair hAnnulus

theorem
    not_forall_exists_some_currentSufficientSameEmbeddingGeometry_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_oneCollarAnnulusCurrentBoundaryData_and_taitEdgeColoring_and_nonempty_selectedBoundaryInteriorCarrier_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.numCollars = 1 ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData) →
            (∃ C : sharedInteriorPairAnnulusGraph.EdgeColoring Color,
              IsTaitEdgeColoring sharedInteriorPairAnnulusGraph C) →
            (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty →
            Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∨
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∨
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∨
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) := by
  intro h
  have hAny :=
    h sharedInteriorPairAnnulusEmbedding sharedInteriorPairAnnulusBoundaryReachabilityData
      sharedInteriorPairDartSuccessorCycleGeometry
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
      (by
        have hcurrent :
            ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData sharedInteriorPairAnnulusEmbedding,
              data.numCollars = 1 ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  sharedInteriorPairAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData := by
          let source : PlanarBoundaryClosedWalkAnnulusBoundarySource
              sharedInteriorPairAnnulusEmbedding :=
            PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              sharedInteriorPairAnnulusBoundaryReachabilityData
              sharedInteriorPairDartSuccessorCycleGeometry
              sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace
          rcases
            exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource source with
            ⟨data, hnum, hboundary⟩
          exact ⟨data, hnum, by
            simpa [source, PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields,
              PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields,
              PlanarBoundaryClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData]
              using hboundary⟩
        exact hcurrent)
      exists_taitEdgeColoring_sharedInteriorPairAnnulusGraph
      selectedBoundaryInteriorEdgeEndpointVertices_nonempty_sharedInteriorPair
  rcases hAny with hHeight | hCollar | hAttached | hWellFounded | hAnnulus
  · exact not_nonempty_planarBoundaryHeightOrderedFacePeelWitnessData_sharedInteriorPair hHeight
  · exact not_nonempty_planarBoundaryCollarLayerFacePeelWitnessData_sharedInteriorPair hCollar
  · exact not_nonempty_attachedBoundaryRootedFacePeelCertificate_sharedInteriorPair hAttached
  · exact not_nonempty_planarBoundaryWellFoundedFacePeelWitnessData_sharedInteriorPair hWellFounded
  · exact not_nonempty_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair hAnnulus

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_twoCollarAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
              data.numCollars = 2 ∧
                data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      not_exists_twoCollar_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData⟩

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_threeCollarAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
              data.numCollars = 3 ∧
                data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      not_exists_threeCollar_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData⟩

theorem
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_and_numCollars_eq_two_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
              data.numCollars = 2 ∧
                data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_and_numCollars_eq_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_annulusCollarGeometry
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_twoCollarAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData

theorem
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_and_numCollars_eq_three_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
              data.numCollars = 3 ∧
                data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_and_numCollars_eq_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_annulusCollarGeometry
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_threeCollarAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_twoCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.numCollars = 2 ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      not_exists_twoCollar_planarBoundaryAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData⟩

theorem
    exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_threeCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
          ¬ ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.numCollars = 3 ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairAnnulusBoundaryReachabilityData,
      sharedInteriorPairDartSuccessorCycleGeometry,
      sharedInteriorPairDartSuccessorCycleGeometry_selectedBoundaryArcOnFace,
      not_exists_threeCollar_planarBoundaryAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData⟩

theorem
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_two_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.numCollars = 2 ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_currentBoundaryData
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_twoCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData

theorem
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_three_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) →
            ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
              data.numCollars = 3 ∧
                data.toPlanarBoundaryAnnulusBoundaryData =
                  boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_currentBoundaryData
      exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_without_threeCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData

theorem
    not_forall_exists_planarBoundaryWellFoundedFacePeelWitnessData_of_closedWalkAnnulusBoundarySource_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) := by
  exact
    not_forall_exists_planarBoundaryWellFoundedFacePeelWitnessData_of_exists_embedding_closedWalkAnnulusBoundarySource_without_wellFoundedFacePeelWitnessData
      exists_embedding_closedWalkAnnulusBoundarySource_without_wellFoundedFacePeelWitnessData_sharedInteriorPair

theorem
    not_exists_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData :
    ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding,
        data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
          sharedInteriorPairBoundaryData := by
  rintro ⟨data, hboundary⟩
  have hpos : 0 < data.numCollars := data.toPlanarBoundaryAnnulusDecomposition.numCollars_pos
  have hle : data.numCollars ≤ 3 :=
    numCollars_le_three_of_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair data
  have hcases : data.numCollars = 1 ∨ data.numCollars = 2 ∨ data.numCollars = 3 := by
    omega
  rcases hcases with h1 | h2 | h3
  · exact
      not_exists_oneCollar_planarBoundaryAnnulusCollarGeometry_sharedInteriorPair
        ⟨data, h1⟩
  · exact
      not_exists_twoCollar_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData
        ⟨data, h2, hboundary⟩
  · exact
      not_exists_threeCollar_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData
        ⟨data, h3, hboundary⟩

theorem
    closedWalkAnnulusBoundarySource_without_annulusCollarGeometry_with_sharedInteriorPairBoundaryData :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource sharedInteriorPairAnnulusEmbedding) ∧
      ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry sharedInteriorPairAnnulusEmbedding,
          data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
            sharedInteriorPairBoundaryData := by
  exact
    ⟨nonempty_sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_exists_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_without_annulusCollarGeometry_with_sharedInteriorPairBoundaryData :
    ∃ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ¬ ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    ⟨sharedInteriorPairAnnulusEmbedding,
      sharedInteriorPairClosedWalkAnnulusBoundarySource,
      not_exists_planarBoundaryAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData⟩

/-- There is no universal same-embedding derivation from the honest closed-walk annulus source to
weak annulus collar geometry preserving the source's own boundary split. The `sharedInteriorPair`
source model already carries the full source package, but the same embedding admits no weak collar
geometry with that extracted annulus boundary data at all. -/
theorem
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_of_exists_embedding_closedWalkAnnulusBoundarySource_without_annulusCollarGeometry
      exists_embedding_closedWalkAnnulusBoundarySource_without_annulusCollarGeometry_with_sharedInteriorPairBoundaryData

theorem
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_and_numCollars_eq_two_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
            data.numCollars = 2 ∧
              data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_and_numCollars_eq_of_exists_embedding_closedWalkAnnulusBoundarySource_without_annulusCollarGeometry
      exists_embedding_closedWalkAnnulusBoundarySource_without_twoCollarAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData

theorem
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_and_numCollars_eq_three_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
            data.numCollars = 3 ∧
              data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_exists_planarBoundaryAnnulusCollarGeometry_with_sourceBoundaryData_and_numCollars_eq_of_exists_embedding_closedWalkAnnulusBoundarySource_without_annulusCollarGeometry
      exists_embedding_closedWalkAnnulusBoundarySource_without_threeCollarAnnulusCollarGeometry_with_sharedInteriorPairBoundaryData

theorem
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_two_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 2 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_of_exists_embedding_closedWalkAnnulusBoundarySource_without_currentBoundaryData
      exists_embedding_closedWalkAnnulusBoundarySource_without_twoCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData

theorem
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_three_sharedInteriorPair :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary sharedInteriorPairAnnulusGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
            data.numCollars = 3 ∧
              data.toPlanarBoundaryAnnulusBoundaryData =
                source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    not_forall_exists_planarBoundaryAnnulusCurrentBoundaryData_with_sourceBoundaryData_and_numCollars_eq_of_exists_embedding_closedWalkAnnulusBoundarySource_without_currentBoundaryData
      exists_embedding_closedWalkAnnulusBoundarySource_without_threeCollarAnnulusCurrentBoundaryData_with_sharedInteriorPairBoundaryData

end Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

end Mettapedia.GraphTheory.FourColor
