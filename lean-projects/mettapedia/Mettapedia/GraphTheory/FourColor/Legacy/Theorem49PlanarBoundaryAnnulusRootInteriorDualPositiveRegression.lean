import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49PlanarBoundaryAnnulusRootInteriorDualPositiveRegression

open Theorem49ForcingInteriorEdgeObstruction

/-- A degenerate closed-walk annulus source with two disconnected triangular boundary
components and no interior edge support.  This is the positive counterpart to the two-band
obstruction: the source-fixed boundary-face roots cover and separate the empty interior dual, so
the no-interior source-fixed parent constructor genuinely instantiates. -/
def twoTriangleAnnulusGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 0), s(3, 4), s(4, 5), s(5, 3)} :
      Set (Sym2 (Fin 6)))

def tta01 : twoTriangleAnnulusGraph.edgeSet := ⟨s(0, 1), by
  simp [twoTriangleAnnulusGraph]⟩

def tta12 : twoTriangleAnnulusGraph.edgeSet := ⟨s(1, 2), by
  simp [twoTriangleAnnulusGraph]⟩

def tta20 : twoTriangleAnnulusGraph.edgeSet := ⟨s(2, 0), by
  simp [twoTriangleAnnulusGraph]⟩

def tta34 : twoTriangleAnnulusGraph.edgeSet := ⟨s(3, 4), by
  simp [twoTriangleAnnulusGraph]⟩

def tta45 : twoTriangleAnnulusGraph.edgeSet := ⟨s(4, 5), by
  simp [twoTriangleAnnulusGraph]⟩

def tta53 : twoTriangleAnnulusGraph.edgeSet := ⟨s(5, 3), by
  simp [twoTriangleAnnulusGraph]⟩

theorem twoTriangleAnnulus_edge_eq
    (e : twoTriangleAnnulusGraph.edgeSet) :
    e = tta01 ∨ e = tta12 ∨ e = tta20 ∨
      e = tta34 ∨ e = tta45 ∨ e = tta53 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 0) ∨
          e.1 = s(3, 4) ∨ e.1 = s(4, 5) ∨ e.1 = s(5, 3)) ∧
        ¬ e.1.IsDiag := by
    simpa [twoTriangleAnnulusGraph] using e.2
  rcases h.1 with h01 | h12 | h20 | h34 | h45 | h53
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr <| Or.inl (Subtype.ext h12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h34)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext h53)

abbrev TwoTriangleAnnulusFace := Fin 2

def twoTriangleAnnulusFaces : Finset TwoTriangleAnnulusFace := Finset.univ

def twoTriangleAnnulusFaceBoundary :
    TwoTriangleAnnulusFace → Finset twoTriangleAnnulusGraph.edgeSet
  | ⟨0, _⟩ => {tta01, tta12, tta20}
  | ⟨1, _⟩ => {tta34, tta45, tta53}

theorem totalIncidenceCount_tta01 :
    totalIncidenceCount twoTriangleAnnulusFaceBoundary twoTriangleAnnulusFaces tta01 = 1 := by
  decide

theorem totalIncidenceCount_tta12 :
    totalIncidenceCount twoTriangleAnnulusFaceBoundary twoTriangleAnnulusFaces tta12 = 1 := by
  decide

theorem totalIncidenceCount_tta20 :
    totalIncidenceCount twoTriangleAnnulusFaceBoundary twoTriangleAnnulusFaces tta20 = 1 := by
  decide

theorem totalIncidenceCount_tta34 :
    totalIncidenceCount twoTriangleAnnulusFaceBoundary twoTriangleAnnulusFaces tta34 = 1 := by
  decide

theorem totalIncidenceCount_tta45 :
    totalIncidenceCount twoTriangleAnnulusFaceBoundary twoTriangleAnnulusFaces tta45 = 1 := by
  decide

theorem totalIncidenceCount_tta53 :
    totalIncidenceCount twoTriangleAnnulusFaceBoundary twoTriangleAnnulusFaces tta53 = 1 := by
  decide

def twoTriangleAnnulusEmbedding : PlaneEmbeddingWithBoundary twoTriangleAnnulusGraph where
  Face := TwoTriangleAnnulusFace
  faceDecidableEq := inferInstance
  faces := twoTriangleAnnulusFaces
  faceBoundary := twoTriangleAnnulusFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases twoTriangleAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases twoTriangleAnnulus_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

def twoTriangleOuterFace : AmbientFace twoTriangleAnnulusEmbedding.faces :=
  ⟨(0 : TwoTriangleAnnulusFace), by
    simp [twoTriangleAnnulusEmbedding, twoTriangleAnnulusFaces]⟩

def twoTriangleInnerFace : AmbientFace twoTriangleAnnulusEmbedding.faces :=
  ⟨(1 : TwoTriangleAnnulusFace), by
    simp [twoTriangleAnnulusEmbedding, twoTriangleAnnulusFaces]⟩

theorem twoTriangleAnnulusFace_cases
    (f : AmbientFace twoTriangleAnnulusEmbedding.faces) :
    f = twoTriangleOuterFace ∨ f = twoTriangleInnerFace := by
  rcases f with ⟨f, _hfmem⟩
  change TwoTriangleAnnulusFace at f
  fin_cases f
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr (Subtype.ext rfl)

theorem tta01_mem_selectedBoundarySupport :
    tta01 ∈ selectedBoundarySupport
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleAnnulusEmbedding.faces
      twoTriangleAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, by simpa [twoTriangleAnnulusEmbedding] using totalIncidenceCount_tta01⟩

theorem tta12_mem_selectedBoundarySupport :
    tta12 ∈ selectedBoundarySupport
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleAnnulusEmbedding.faces
      twoTriangleAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, by simpa [twoTriangleAnnulusEmbedding] using totalIncidenceCount_tta12⟩

theorem tta20_mem_selectedBoundarySupport :
    tta20 ∈ selectedBoundarySupport
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleAnnulusEmbedding.faces
      twoTriangleAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, by simpa [twoTriangleAnnulusEmbedding] using totalIncidenceCount_tta20⟩

theorem tta34_mem_selectedBoundarySupport :
    tta34 ∈ selectedBoundarySupport
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleAnnulusEmbedding.faces
      twoTriangleAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, by simpa [twoTriangleAnnulusEmbedding] using totalIncidenceCount_tta34⟩

theorem tta45_mem_selectedBoundarySupport :
    tta45 ∈ selectedBoundarySupport
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleAnnulusEmbedding.faces
      twoTriangleAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, by simpa [twoTriangleAnnulusEmbedding] using totalIncidenceCount_tta45⟩

theorem tta53_mem_selectedBoundarySupport :
    tta53 ∈ selectedBoundarySupport
      twoTriangleAnnulusEmbedding.faceBoundary twoTriangleAnnulusEmbedding.faces
      twoTriangleAnnulusEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, by simpa [twoTriangleAnnulusEmbedding] using totalIncidenceCount_tta53⟩

theorem twoTriangleAnnulus_interiorEdgeSupport_eq_empty :
    interiorEdgeSupport twoTriangleAnnulusEmbedding.faceBoundary
      twoTriangleAnnulusEmbedding.faces = ∅ := by
  ext e
  rcases twoTriangleAnnulus_edge_eq e with rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

def twoTriangleOuterRoot : PlanarBoundaryEdgeVertex twoTriangleAnnulusEmbedding :=
  ⟨tta01, tta01_mem_selectedBoundarySupport⟩

def twoTriangleInnerRoot : PlanarBoundaryEdgeVertex twoTriangleAnnulusEmbedding :=
  ⟨tta34, tta34_mem_selectedBoundarySupport⟩

def twoTriangleBoundaryLabel (e : PlanarBoundaryEdgeVertex twoTriangleAnnulusEmbedding) :
    Bool :=
  if e.1 = tta34 ∨ e.1 = tta45 ∨ e.1 = tta53 then true else false

theorem twoTriangle_boundaryEdge_eq
    (e : PlanarBoundaryEdgeVertex twoTriangleAnnulusEmbedding) :
    e = ⟨tta01, tta01_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tta12, tta12_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tta20, tta20_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tta34, tta34_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tta45, tta45_mem_selectedBoundarySupport⟩ ∨
      e = ⟨tta53, tta53_mem_selectedBoundarySupport⟩ := by
  rcases twoTriangleAnnulus_edge_eq e.1 with h01 | h12 | h20 | h34 | h45 | h53
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr <| Or.inl (Subtype.ext h12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h34)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext h53)

theorem twoTriangleBoundaryAdj_preserves_label :
    ∀ ⦃e f : PlanarBoundaryEdgeVertex twoTriangleAnnulusEmbedding⦄,
      (planarBoundarySupportEndpointAdjGraph twoTriangleAnnulusEmbedding).Adj e f →
        twoTriangleBoundaryLabel e = twoTriangleBoundaryLabel f := by
  intro e f hadj
  rcases twoTriangle_boundaryEdge_eq e with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases twoTriangle_boundaryEdge_eq f with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact False.elim
          (by
            rcases hadj with ⟨_, v, hvE, hvF⟩
            fin_cases v <;>
              simp [tta01, tta12, tta20, tta34, tta45, tta53] at hvE hvF)

theorem twoTriangleOuterRoot_ne_innerRoot :
    twoTriangleOuterRoot ≠ twoTriangleInnerRoot := by
  intro h
  have := congrArg Subtype.val h
  simp [twoTriangleOuterRoot, twoTriangleInnerRoot, tta01, tta34] at this

def twoTriangleAnnulusBoundaryReachabilityData :
    PlanarBoundaryAnnulusBoundaryReachabilityData twoTriangleAnnulusEmbedding where
  outerRoot := twoTriangleOuterRoot
  innerRoot := twoTriangleInnerRoot
  hroots_ne := twoTriangleOuterRoot_ne_innerRoot
  hcoverRoots := by
    intro e
    rcases twoTriangle_boundaryEdge_eq e with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨twoTriangleOuterRoot, by simp [twoTriangleOuterRoot_ne_innerRoot],
        SimpleGraph.Reachable.refl _⟩
    · refine ⟨twoTriangleOuterRoot, by simp [twoTriangleOuterRoot_ne_innerRoot], ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph twoTriangleAnnulusEmbedding).Adj
            ⟨tta12, tta12_mem_selectedBoundarySupport⟩
            twoTriangleOuterRoot := by
        refine ⟨?_, 1, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [twoTriangleOuterRoot, tta12, tta01] at this
        · simp [tta12]
        · simp [twoTriangleOuterRoot, tta01]
      exact hadj.reachable
    · refine ⟨twoTriangleOuterRoot, by simp [twoTriangleOuterRoot_ne_innerRoot], ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph twoTriangleAnnulusEmbedding).Adj
            ⟨tta20, tta20_mem_selectedBoundarySupport⟩
            twoTriangleOuterRoot := by
        refine ⟨?_, 0, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [twoTriangleOuterRoot, tta20, tta01] at this
        · simp [tta20]
        · simp [twoTriangleOuterRoot, tta01]
      exact hadj.reachable
    · refine ⟨twoTriangleInnerRoot, by simp, SimpleGraph.Reachable.refl _⟩
    · refine ⟨twoTriangleInnerRoot, by simp, ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph twoTriangleAnnulusEmbedding).Adj
            ⟨tta45, tta45_mem_selectedBoundarySupport⟩
            twoTriangleInnerRoot := by
        refine ⟨?_, 4, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [twoTriangleInnerRoot, tta45, tta34] at this
        · simp [tta45]
        · simp [twoTriangleInnerRoot, tta34]
      exact hadj.reachable
    · refine ⟨twoTriangleInnerRoot, by simp, ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph twoTriangleAnnulusEmbedding).Adj
            ⟨tta53, tta53_mem_selectedBoundarySupport⟩
            twoTriangleInnerRoot := by
        refine ⟨?_, 3, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [twoTriangleInnerRoot, tta53, tta34] at this
        · simp [tta53]
        · simp [twoTriangleInnerRoot, tta34]
      exact hadj.reachable
  hsepRoots := by
    intro r s hr hs hreach
    have hlabelEq :
        twoTriangleBoundaryLabel r = twoTriangleBoundaryLabel s :=
      eq_of_reachable_of_eq_on_adj
        (planarBoundarySupportEndpointAdjGraph twoTriangleAnnulusEmbedding)
        twoTriangleBoundaryLabel
        (by
          intro u v huv
          exact twoTriangleBoundaryAdj_preserves_label huv)
        hreach
    have hOuterLabel : twoTriangleBoundaryLabel twoTriangleOuterRoot = false := by
      decide
    have hInnerLabel : twoTriangleBoundaryLabel twoTriangleInnerRoot = true := by
      decide
    have hr_cases : r = twoTriangleOuterRoot ∨ r = twoTriangleInnerRoot := by
      simpa [twoTriangleOuterRoot_ne_innerRoot] using hr
    have hs_cases : s = twoTriangleOuterRoot ∨ s = twoTriangleInnerRoot := by
      simpa [twoTriangleOuterRoot_ne_innerRoot] using hs
    rcases hr_cases with rfl | rfl <;> rcases hs_cases with rfl | rfl
    · rfl
    · rw [hOuterLabel, hInnerLabel] at hlabelEq
      cases hlabelEq
    · rw [hInnerLabel, hOuterLabel] at hlabelEq
      cases hlabelEq
    · rfl

def ttaDart01 : twoTriangleAnnulusGraph.Dart := ⟨((0 : Fin 6), 1), by
  simp [twoTriangleAnnulusGraph]⟩

def ttaDart12 : twoTriangleAnnulusGraph.Dart := ⟨((1 : Fin 6), 2), by
  simp [twoTriangleAnnulusGraph]⟩

def ttaDart20 : twoTriangleAnnulusGraph.Dart := ⟨((2 : Fin 6), 0), by
  simp [twoTriangleAnnulusGraph]⟩

def ttaDart34 : twoTriangleAnnulusGraph.Dart := ⟨((3 : Fin 6), 4), by
  simp [twoTriangleAnnulusGraph]⟩

def ttaDart45 : twoTriangleAnnulusGraph.Dart := ⟨((4 : Fin 6), 5), by
  simp [twoTriangleAnnulusGraph]⟩

def ttaDart53 : twoTriangleAnnulusGraph.Dart := ⟨((5 : Fin 6), 3), by
  simp [twoTriangleAnnulusGraph]⟩

macro "tta_dart_cycle" : tactic =>
  `(tactic| simp [SimpleGraph.DartAdj, ttaDart01, ttaDart12, ttaDart20,
    ttaDart34, ttaDart45, ttaDart53])

def twoTriangleOuterFacePureDartCycle
    (hf : (0 : TwoTriangleAnnulusFace) ∈ twoTriangleAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoTriangleAnnulusEmbedding ⟨(0 : TwoTriangleAnnulusFace), hf⟩ where
  darts := [ttaDart01, ttaDart12, ttaDart20]
  hnonempty := by simp
  hclosed := by tta_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [twoTriangleAnnulusEmbedding, twoTriangleAnnulusFaceBoundary,
        tta01, tta12, tta20, ttaDart01, ttaDart12, ttaDart20]
  hface_sub := by
    intro e he
    have he' : e = tta01 ∨ e = tta12 ∨ e = tta20 := by
      simpa [twoTriangleAnnulusEmbedding, twoTriangleAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [tta01, tta12, tta20, ttaDart01, ttaDart12, ttaDart20]

def twoTriangleInnerFacePureDartCycle
    (hf : (1 : TwoTriangleAnnulusFace) ∈ twoTriangleAnnulusEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      twoTriangleAnnulusEmbedding ⟨(1 : TwoTriangleAnnulusFace), hf⟩ where
  darts := [ttaDart34, ttaDart45, ttaDart53]
  hnonempty := by simp
  hclosed := by tta_dart_cycle
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [twoTriangleAnnulusEmbedding, twoTriangleAnnulusFaceBoundary,
        tta34, tta45, tta53, ttaDart34, ttaDart45, ttaDart53]
  hface_sub := by
    intro e he
    have he' : e = tta34 ∨ e = tta45 ∨ e = tta53 := by
      simpa [twoTriangleAnnulusEmbedding, twoTriangleAnnulusFaceBoundary] using he
    rcases he' with rfl | rfl | rfl <;>
      simp [tta34, tta45, tta53, ttaDart34, ttaDart45, ttaDart53]

def twoTriangleAnnulusPureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry twoTriangleAnnulusEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change TwoTriangleAnnulusFace at f
    by_cases h0 : f = (0 : TwoTriangleAnnulusFace)
    · subst f
      exact twoTriangleOuterFacePureDartCycle hfmem
    · have h1 : f = (1 : TwoTriangleAnnulusFace) := by
        fin_cases f
        · exact False.elim (h0 rfl)
        · rfl
      subst f
      exact twoTriangleInnerFacePureDartCycle hfmem

def twoTriangleAnnulusClosedWalkEmbeddingData :
    PlanarBoundaryClosedWalkEmbeddingData twoTriangleAnnulusEmbedding :=
  twoTriangleAnnulusPureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

theorem twoTriangleAnnulusClosedWalkEmbeddingData_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace twoTriangleAnnulusEmbedding.faces,
      (twoTriangleAnnulusClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f := by
  intro f
  rcases twoTriangleAnnulusFace_cases f with rfl | rfl
  ·
    refine ⟨[tta01, tta12, tta20], ?_, ?_⟩
    · decide
    · intro e
      rcases twoTriangleAnnulus_edge_eq e with rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  ·
    refine ⟨[tta34, tta45, tta53], ?_, ?_⟩
    · decide
    · intro e
      rcases twoTriangleAnnulus_edge_eq e with rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide

def twoTriangleClosedWalkAnnulusBoundarySource :
    PlanarBoundaryClosedWalkAnnulusBoundarySource twoTriangleAnnulusEmbedding :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields
    twoTriangleAnnulusBoundaryReachabilityData
    twoTriangleAnnulusClosedWalkEmbeddingData
    twoTriangleAnnulusClosedWalkEmbeddingData_selectedBoundaryArcOnFace

noncomputable def twoTriangleAnnulusBoundaryData :
    PlanarBoundaryAnnulusBoundaryData twoTriangleAnnulusEmbedding :=
  twoTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData

theorem twoTriangleAnnulusBoundaryFaceRoots_eq_univ :
    twoTriangleClosedWalkAnnulusBoundarySource.boundaryFaceRoots = Finset.univ := by
  ext f
  constructor
  · intro _hf
    simp
  · intro _hf
    change f ∈ twoTriangleAnnulusBoundaryData.outerBoundaryFaces ∪
      twoTriangleAnnulusBoundaryData.innerBoundaryFaces
    apply (twoTriangleAnnulusBoundaryData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_iff).2
    rcases twoTriangleAnnulusFace_cases f with rfl | rfl
    · exact ⟨tta01, by decide, tta01_mem_selectedBoundarySupport⟩
    · exact ⟨tta34, by decide, tta34_mem_selectedBoundarySupport⟩

theorem rootSetCovers_twoTriangleAnnulusBoundaryFaceRoots :
    RootSetCovers
      (interiorDualGraph twoTriangleAnnulusEmbedding.faceBoundary
        twoTriangleAnnulusEmbedding.faces)
      twoTriangleClosedWalkAnnulusBoundarySource.boundaryFaceRoots := by
  intro f
  refine ⟨f, ?_, SimpleGraph.Reachable.refl f⟩
  rw [twoTriangleAnnulusBoundaryFaceRoots_eq_univ]
  simp

theorem twoTriangleAnnulusInteriorDual_eq_bot :
    interiorDualGraph twoTriangleAnnulusEmbedding.faceBoundary
      twoTriangleAnnulusEmbedding.faces = ⊥ := by
  ext f g
  constructor
  · intro hfg
    rcases (interiorDualGraph_adj_iff twoTriangleAnnulusEmbedding.faceBoundary
        twoTriangleAnnulusEmbedding.faces).1 hfg with
      ⟨_hneq, e, heInterior, _hef, _heg⟩
    simp [twoTriangleAnnulus_interiorEdgeSupport_eq_empty] at heInterior
  · intro hfg
    simp at hfg

theorem rootSetSeparated_twoTriangleAnnulusBoundaryFaceRoots :
    RootSetSeparated
      (interiorDualGraph twoTriangleAnnulusEmbedding.faceBoundary
        twoTriangleAnnulusEmbedding.faces)
      twoTriangleClosedWalkAnnulusBoundarySource.boundaryFaceRoots := by
  intro r s _hr _hs hreach
  have hreachBot :
      (⊥ : SimpleGraph (AmbientFace twoTriangleAnnulusEmbedding.faces)).Reachable r s := by
    simpa [twoTriangleAnnulusInteriorDual_eq_bot] using hreach
  exact (SimpleGraph.reachable_bot).1 hreachBot

/-- Positive source-fixed parent sufficiency cross-check: the concrete closed-walk source with
empty interior support instantiates the parent-oriented IDBRAD replacement on the same
embedding. -/
noncomputable def twoTriangleClosedWalkSourceInteriorDualBoundaryRootParentPeelData :
    InteriorDualBoundaryRootParentPeelData twoTriangleAnnulusEmbedding.faces
      twoTriangleAnnulusEmbedding.faceBoundary :=
  interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
    twoTriangleClosedWalkAnnulusBoundarySource
    rootSetCovers_twoTriangleAnnulusBoundaryFaceRoots
    rootSetSeparated_twoTriangleAnnulusBoundaryFaceRoots
    twoTriangleAnnulus_interiorEdgeSupport_eq_empty

/-- Graph-level positive cross-check for the no-interior source-fixed sufficiency branch. -/
theorem admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_twoTriangleAnnulusGraph :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData twoTriangleAnnulusGraph := by
  exact
    admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      ⟨twoTriangleAnnulusEmbedding,
        twoTriangleClosedWalkAnnulusBoundarySource,
        rootSetCovers_twoTriangleAnnulusBoundaryFaceRoots,
        rootSetSeparated_twoTriangleAnnulusBoundaryFaceRoots,
        twoTriangleAnnulus_interiorEdgeSupport_eq_empty⟩

/-- The same positive source-fixed base case also reaches the boundary-free selector surface used
by the replacement-construction lane. -/
noncomputable def twoTriangleClosedWalkSourceBoundaryFreeIncidentFaceSelector :
    BoundaryFreeIncidentFaceSelector twoTriangleAnnulusEmbedding :=
  boundaryFreeIncidentFaceSelectorOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
    twoTriangleClosedWalkAnnulusBoundarySource
    rootSetCovers_twoTriangleAnnulusBoundaryFaceRoots
    rootSetSeparated_twoTriangleAnnulusBoundaryFaceRoots
    twoTriangleAnnulus_interiorEdgeSupport_eq_empty

theorem nonempty_boundaryFreeIncidentFaceSelector_twoTriangleAnnulusEmbedding :
    Nonempty (BoundaryFreeIncidentFaceSelector twoTriangleAnnulusEmbedding) :=
  ⟨twoTriangleClosedWalkSourceBoundaryFreeIncidentFaceSelector⟩

end Theorem49PlanarBoundaryAnnulusRootInteriorDualPositiveRegression

end Mettapedia.GraphTheory.FourColor
