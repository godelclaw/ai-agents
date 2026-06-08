import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometry
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceProjection
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryCollarPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVerticesEndpointObstruction
import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49PlanarBoundaryAnnulusHonestGeometryRegression

open Theorem49InteriorVerticesEndpointObstruction

theorem false_of_four_pairwise_distinct_nonzero_colors
    {a b c d : Color} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : False := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero d hd with rfl | rfl | rfl <;>
    simp_all

/-- The honest `diamondWithTriangle` source model also admits a one-collar annulus geometry: all
three ambient faces are peeled in a single collar, with the diamond pair using the shared
interior edge as witness and the separate triangle using one inner-boundary edge.  This is the
weakest genuine annulus geometry surface now relevant to the ground-up certificate route. -/
def diamondWithTriangleOuterAmbientBoundary : Finset diamondWithTriangleGraph.edgeSet :=
  {dt01, dt02, dt13, dt23}

def diamondWithTriangleInnerAmbientBoundary : Finset diamondWithTriangleGraph.edgeSet :=
  {dt45, dt56, dt64}

def diamondWithTriangleFace0 : AmbientFace diamondWithTriangleEmbedding.faces :=
  ⟨(0 : DiamondWithTriangleFace), by
    simp [diamondWithTriangleEmbedding, diamondWithTriangleFaces]⟩

def diamondWithTriangleFace1 : AmbientFace diamondWithTriangleEmbedding.faces :=
  ⟨(1 : DiamondWithTriangleFace), by
    simp [diamondWithTriangleEmbedding, diamondWithTriangleFaces]⟩

def diamondWithTriangleFace2 : AmbientFace diamondWithTriangleEmbedding.faces :=
  ⟨(2 : DiamondWithTriangleFace), by
    simp [diamondWithTriangleEmbedding, diamondWithTriangleFaces]⟩

def diamondWithTriangleBoundaryData : PlanarBoundaryAnnulusBoundaryData diamondWithTriangleEmbedding := by
  refine
    { outerAmbientBoundary := diamondWithTriangleOuterAmbientBoundary
      innerAmbientBoundary := diamondWithTriangleInnerAmbientBoundary
      houterAmbientBoundaryNonempty := by decide
      hinnerAmbientBoundaryNonempty := by decide
      houterAmbientBoundarySubset := by decide
      hinnerAmbientBoundarySubset := by decide
      hambientBoundaryCover := by decide
      hambientBoundaryDisjoint := by decide }

def diamondWithTriangleOneCollarFaces :
    Fin 1 → Finset (AmbientFace diamondWithTriangleEmbedding.faces)
  | _ => {diamondWithTriangleFace0, diamondWithTriangleFace1, diamondWithTriangleFace2}

def diamondWithTriangleOneCollarBoundaryCycle : Fin 2 → Finset diamondWithTriangleGraph.edgeSet
  | ⟨0, _⟩ => diamondWithTriangleOuterAmbientBoundary
  | ⟨1, _⟩ => diamondWithTriangleInnerAmbientBoundary

def diamondWithTriangleOneCollarDecomposition :
    PlanarBoundaryAnnulusDecomposition diamondWithTriangleEmbedding := by
  refine
    { toPlanarBoundaryAnnulusBoundaryData := diamondWithTriangleBoundaryData
      numCollars := 1
      collarFaces := diamondWithTriangleOneCollarFaces
      remainderFaces := laterLayerFaces diamondWithTriangleOneCollarFaces
      boundaryCycle := diamondWithTriangleOneCollarBoundaryCycle
      hfaceCover := by decide
      hdisjoint := by decide
      hremainder := by
        intro i
        rfl
      houterBoundary := by decide
      hinnerBoundary := by decide
      hcurrentBoundaryCover := by decide
      hremainderBoundaryCover := by decide
      hcurrentInnerAmbientBoundary := by decide
      hremainderInnerAmbientBoundary := by decide
      hintermediateBoundaryInterior := by decide
      hintermediateBoundaryNonempty := by decide
      hboundaryCycleDisjoint := by decide
      hambientOuterBoundary := by decide
      hambientInnerBoundary := by decide }

def diamondWithTriangleOneCollarWitnessEdge :
    AmbientFace diamondWithTriangleEmbedding.faces → diamondWithTriangleGraph.edgeSet
  | ⟨⟨0, _⟩, _⟩ => dt12
  | ⟨⟨1, _⟩, _⟩ => dt12
  | ⟨⟨2, _⟩, _⟩ => dt45

def diamondWithTriangleOneCollarGeometry :
    PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding := by
  refine
    { toPlanarBoundaryAnnulusDecomposition := diamondWithTriangleOneCollarDecomposition
      witnessEdge := diamondWithTriangleOneCollarWitnessEdge
      hcover := by decide
      hwitness := by decide
      hrest := by decide
      hfrontier := by decide }

/-- The same honest closed-walk source carries the canonical one-collar witness choice on the
boundary split extracted from that source: the shared diamond edge witnesses the two diamond
faces, while one inner triangle edge witnesses the isolated triangle face.  This is a positive
source-side construction, complementary to the shared-interior-pair failed converse. -/
noncomputable def diamondWithTriangleClosedWalkCanonicalWitnessChoice :
    PlanarBoundaryCanonicalWitnessChoice
      diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData := by
  classical
  refine
    { witnessEdge := diamondWithTriangleOneCollarWitnessEdge
      hcover := by decide
      hwitness := by decide
      hrest := ?_ }
  intro f e he
  have heSelected :
      e ∈ selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces := by
    rcases diamondWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact dt01_mem_selectedBoundarySupport
    · exfalso
      fin_cases f <;>
        simp [diamondWithTriangleOneCollarWitnessEdge, diamondWithTriangleEmbedding,
          diamondWithTriangleFaceBoundary, dt12, dt45, dt56, dt64] at he
    · exact dt02_mem_selectedBoundarySupport
    · exact dt13_mem_selectedBoundarySupport
    · exact dt23_mem_selectedBoundarySupport
    · exact dt45_mem_selectedBoundarySupport
    · exact dt56_mem_selectedBoundarySupport
    · exact dt64_mem_selectedBoundarySupport
  exact
    diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData
      |>.hambientBoundaryCover heSelected

theorem diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice :
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) := by
  exact ⟨diamondWithTriangleClosedWalkCanonicalWitnessChoice⟩

theorem exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    ⟨diamondWithTriangleEmbedding, diamondWithTriangleClosedWalkAnnulusBoundarySource,
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice⟩

theorem
    diamondWithTriangleGraph_admitsPlanarBoundaryAnnulusWitnessAssignment_via_closedWalkCanonicalWitnessChoice :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment diamondWithTriangleGraph := by
  exact
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_planarBoundaryCanonicalWitnessChoice
      ⟨diamondWithTriangleEmbedding,
        diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData,
        diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice⟩

def diamondWithTriangleEdgeColor (e : diamondWithTriangleGraph.edgeSet) : Color :=
  if e = dt12 ∨ e = dt45 then red
  else if e = dt01 ∨ e = dt23 ∨ e = dt56 then blue
  else purple

def diamondWithTriangleTaitEdgeColoring : diamondWithTriangleGraph.EdgeColoring Color :=
  Coloring.mk diamondWithTriangleEdgeColor (by
    intro e f hadj
    rcases diamondWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases diamondWithTriangle_edge_eq f with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [diamondWithTriangleEdgeColor, SimpleGraph.lineGraph_adj_iff_exists,
        diamondWithTriangleGraph, dt01, dt12, dt02, dt13, dt23, dt45, dt56, dt64,
        red, blue, purple] at hadj ⊢)

theorem diamondWithTriangleTaitEdgeColoring_isTait :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring := by
  intro e
  change diamondWithTriangleEdgeColor e ≠ 0
  rcases diamondWithTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [diamondWithTriangleEdgeColor, diamondWithTriangleGraph, dt01, dt12, dt02,
      dt13, dt23, dt45, dt56, dt64, red, blue, purple]

theorem exists_taitEdgeColoring_diamondWithTriangleGraph :
    ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
      IsTaitEdgeColoring diamondWithTriangleGraph C := by
  exact ⟨diamondWithTriangleTaitEdgeColoring, diamondWithTriangleTaitEdgeColoring_isTait⟩

theorem diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
      diamondWithTriangleTaitEdgeColoring := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusCollarGeometry
      (G := diamondWithTriangleGraph) diamondWithTriangleOneCollarGeometry
      diamondWithTriangleTaitEdgeColoring diamondWithTriangleTaitEdgeColoring_isTait

/-- A second positive honest-source model: two diamond cells chained along the same outer
boundary component, plus a disjoint triangular inner boundary component.  Unlike
`diamondWithTriangle`, this model has two distinct interior edges, so the canonical witness
choice below is a genuine new finite positive instance rather than a re-use of the one-interior
edge example. -/
def chainedDiamondsWithTriangleGraph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(0, 2), s(1, 3), s(2, 3),
        s(3, 4), s(4, 5), s(3, 5), s(4, 6), s(5, 6),
        s(7, 8), s(8, 9), s(9, 7)} : Set (Sym2 (Fin 10)))

def cdt01 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(0, 1), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdt12 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(1, 2), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdt02 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(0, 2), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdt13 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(1, 3), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdt23 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(2, 3), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdt34 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(3, 4), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdt45 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(4, 5), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdt35 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(3, 5), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdt46 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(4, 6), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdt56 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(5, 6), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdt78 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(7, 8), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdt89 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(8, 9), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdt97 : chainedDiamondsWithTriangleGraph.edgeSet := ⟨s(9, 7), by
  simp [chainedDiamondsWithTriangleGraph]⟩

theorem chainedDiamondsWithTriangle_edge_eq
    (e : chainedDiamondsWithTriangleGraph.edgeSet) :
    e = cdt01 ∨ e = cdt12 ∨ e = cdt02 ∨ e = cdt13 ∨ e = cdt23 ∨
      e = cdt34 ∨ e = cdt45 ∨ e = cdt35 ∨ e = cdt46 ∨ e = cdt56 ∨
        e = cdt78 ∨ e = cdt89 ∨ e = cdt97 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(0, 2) ∨
          e.1 = s(1, 3) ∨ e.1 = s(2, 3) ∨ e.1 = s(3, 4) ∨
          e.1 = s(4, 5) ∨ e.1 = s(3, 5) ∨ e.1 = s(4, 6) ∨
          e.1 = s(5, 6) ∨ e.1 = s(7, 8) ∨ e.1 = s(8, 9) ∨
          e.1 = s(9, 7)) ∧
        ¬ e.1.IsDiag := by
    simpa [chainedDiamondsWithTriangleGraph] using e.2
  rcases h.1 with
    h01 | h12 | h02 | h13 | h23 | h34 | h45 | h35 | h46 | h56 | h78 | h89 | h97
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr <| Or.inl (Subtype.ext h12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h02)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h13)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h23)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h34)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext h35)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inl (Subtype.ext h46)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h56)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h78)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h89)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext h97)

abbrev ChainedDiamondsWithTriangleFace := Fin 5

def chainedDiamondsWithTriangleFaces : Finset ChainedDiamondsWithTriangleFace :=
  Finset.univ

def chainedDiamondsWithTriangleFaceBoundary :
    ChainedDiamondsWithTriangleFace → Finset chainedDiamondsWithTriangleGraph.edgeSet
  | ⟨0, _⟩ => {cdt02, cdt01, cdt12}
  | ⟨1, _⟩ => {cdt23, cdt13, cdt12}
  | ⟨2, _⟩ => {cdt35, cdt34, cdt45}
  | ⟨3, _⟩ => {cdt56, cdt46, cdt45}
  | ⟨4, _⟩ => {cdt78, cdt89, cdt97}

theorem totalIncidenceCount_cdt01 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt01 = 1 := by
  decide

theorem totalIncidenceCount_cdt12 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt12 = 2 := by
  decide

theorem totalIncidenceCount_cdt02 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt02 = 1 := by
  decide

theorem totalIncidenceCount_cdt13 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt13 = 1 := by
  decide

theorem totalIncidenceCount_cdt23 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt23 = 1 := by
  decide

theorem totalIncidenceCount_cdt34 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt34 = 1 := by
  decide

theorem totalIncidenceCount_cdt45 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt45 = 2 := by
  decide

theorem totalIncidenceCount_cdt35 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt35 = 1 := by
  decide

theorem totalIncidenceCount_cdt46 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt46 = 1 := by
  decide

theorem totalIncidenceCount_cdt56 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt56 = 1 := by
  decide

theorem totalIncidenceCount_cdt78 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt78 = 1 := by
  decide

theorem totalIncidenceCount_cdt89 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt89 = 1 := by
  decide

theorem totalIncidenceCount_cdt97 :
    totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
      chainedDiamondsWithTriangleFaces cdt97 = 1 := by
  decide

def chainedDiamondsWithTriangleEmbedding :
    PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph where
  Face := ChainedDiamondsWithTriangleFace
  faceDecidableEq := inferInstance
  faces := chainedDiamondsWithTriangleFaces
  faceBoundary := chainedDiamondsWithTriangleFaceBoundary
  edge_mem_faceSupport := by
    intro e
    rcases chainedDiamondsWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  edge_one_or_two_faces := by
    intro e _he
    rcases chainedDiamondsWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

theorem cdt01_mem_selectedBoundarySupport :
    cdt01 ∈ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt01⟩

theorem cdt02_mem_selectedBoundarySupport :
    cdt02 ∈ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt02⟩

theorem cdt13_mem_selectedBoundarySupport :
    cdt13 ∈ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt13⟩

theorem cdt23_mem_selectedBoundarySupport :
    cdt23 ∈ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt23⟩

theorem cdt34_mem_selectedBoundarySupport :
    cdt34 ∈ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt34⟩

theorem cdt35_mem_selectedBoundarySupport :
    cdt35 ∈ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt35⟩

theorem cdt46_mem_selectedBoundarySupport :
    cdt46 ∈ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt46⟩

theorem cdt56_mem_selectedBoundarySupport :
    cdt56 ∈ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt56⟩

theorem cdt78_mem_selectedBoundarySupport :
    cdt78 ∈ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt78⟩

theorem cdt89_mem_selectedBoundarySupport :
    cdt89 ∈ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt89⟩

theorem cdt97_mem_selectedBoundarySupport :
    cdt97 ∈ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt97⟩

theorem cdt12_mem_interiorEdgeSupport :
    cdt12 ∈ interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt12⟩

theorem cdt45_mem_interiorEdgeSupport :
    cdt45 ∈ interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_interiorEdgeSupport_iff]
  exact ⟨by decide, totalIncidenceCount_cdt45⟩

theorem cdt12_not_mem_selectedBoundarySupport :
    cdt12 ∉ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  rintro ⟨_, hcount⟩
  have hcount' :
      totalIncidenceCount chainedDiamondsWithTriangleEmbedding.faceBoundary
          chainedDiamondsWithTriangleEmbedding.faces cdt12 = 2 := by
    simpa [chainedDiamondsWithTriangleEmbedding] using totalIncidenceCount_cdt12
  rw [hcount'] at hcount
  omega

theorem cdt45_not_mem_selectedBoundarySupport :
    cdt45 ∉ selectedBoundarySupport
      chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
  rw [mem_selectedBoundarySupport_iff]
  rintro ⟨_, hcount⟩
  have hcount' :
      totalIncidenceCount chainedDiamondsWithTriangleEmbedding.faceBoundary
          chainedDiamondsWithTriangleEmbedding.faces cdt45 = 2 := by
    simpa [chainedDiamondsWithTriangleEmbedding] using totalIncidenceCount_cdt45
  rw [hcount'] at hcount
  omega

def chainedDiamondsFace0 : AmbientFace chainedDiamondsWithTriangleEmbedding.faces :=
  ⟨(0 : ChainedDiamondsWithTriangleFace), by
    simp [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaces]⟩

def chainedDiamondsFace1 : AmbientFace chainedDiamondsWithTriangleEmbedding.faces :=
  ⟨(1 : ChainedDiamondsWithTriangleFace), by
    simp [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaces]⟩

def chainedDiamondsFace2 : AmbientFace chainedDiamondsWithTriangleEmbedding.faces :=
  ⟨(2 : ChainedDiamondsWithTriangleFace), by
    simp [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaces]⟩

def chainedDiamondsFace3 : AmbientFace chainedDiamondsWithTriangleEmbedding.faces :=
  ⟨(3 : ChainedDiamondsWithTriangleFace), by
    simp [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaces]⟩

def chainedDiamondsFace4 : AmbientFace chainedDiamondsWithTriangleEmbedding.faces :=
  ⟨(4 : ChainedDiamondsWithTriangleFace), by
    simp [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaces]⟩

def cdtDart20 : chainedDiamondsWithTriangleGraph.Dart := ⟨((2 : Fin 10), 0), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdtDart01 : chainedDiamondsWithTriangleGraph.Dart := ⟨((0 : Fin 10), 1), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdtDart12 : chainedDiamondsWithTriangleGraph.Dart := ⟨((1 : Fin 10), 2), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdtDart23 : chainedDiamondsWithTriangleGraph.Dart := ⟨((2 : Fin 10), 3), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdtDart31 : chainedDiamondsWithTriangleGraph.Dart := ⟨((3 : Fin 10), 1), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdtDart53 : chainedDiamondsWithTriangleGraph.Dart := ⟨((5 : Fin 10), 3), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdtDart34 : chainedDiamondsWithTriangleGraph.Dart := ⟨((3 : Fin 10), 4), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdtDart45 : chainedDiamondsWithTriangleGraph.Dart := ⟨((4 : Fin 10), 5), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdtDart56 : chainedDiamondsWithTriangleGraph.Dart := ⟨((5 : Fin 10), 6), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdtDart64 : chainedDiamondsWithTriangleGraph.Dart := ⟨((6 : Fin 10), 4), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdtDart78 : chainedDiamondsWithTriangleGraph.Dart := ⟨((7 : Fin 10), 8), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdtDart89 : chainedDiamondsWithTriangleGraph.Dart := ⟨((8 : Fin 10), 9), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def cdtDart97 : chainedDiamondsWithTriangleGraph.Dart := ⟨((9 : Fin 10), 7), by
  simp [chainedDiamondsWithTriangleGraph]⟩

def chainedDiamondsFace0PureDartCycle
    (hf : (0 : ChainedDiamondsWithTriangleFace) ∈ chainedDiamondsWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      chainedDiamondsWithTriangleEmbedding ⟨(0 : ChainedDiamondsWithTriangleFace), hf⟩ where
  darts := [cdtDart20, cdtDart01, cdtDart12]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, cdtDart20, cdtDart01, cdtDart12]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaceBoundary,
        cdt02, cdt01, cdt12, cdtDart20, cdtDart01, cdtDart12]
  hface_sub := by
    intro e he
    have he' : e = cdt02 ∨ e = cdt01 ∨ e = cdt12 := by
      simpa [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaceBoundary]
        using he
    rcases he' with rfl | rfl | rfl <;>
      simp [cdt02, cdt01, cdt12, cdtDart20, cdtDart01, cdtDart12]

def chainedDiamondsFace1PureDartCycle
    (hf : (1 : ChainedDiamondsWithTriangleFace) ∈ chainedDiamondsWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      chainedDiamondsWithTriangleEmbedding ⟨(1 : ChainedDiamondsWithTriangleFace), hf⟩ where
  darts := [cdtDart23, cdtDart31, cdtDart12]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, cdtDart23, cdtDart31, cdtDart12]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaceBoundary,
        cdt23, cdt13, cdt12, cdtDart23, cdtDart31, cdtDart12]
  hface_sub := by
    intro e he
    have he' : e = cdt23 ∨ e = cdt13 ∨ e = cdt12 := by
      simpa [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaceBoundary]
        using he
    rcases he' with rfl | rfl | rfl <;>
      simp [cdt23, cdt13, cdt12, cdtDart23, cdtDart31, cdtDart12]

def chainedDiamondsFace2PureDartCycle
    (hf : (2 : ChainedDiamondsWithTriangleFace) ∈ chainedDiamondsWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      chainedDiamondsWithTriangleEmbedding ⟨(2 : ChainedDiamondsWithTriangleFace), hf⟩ where
  darts := [cdtDart53, cdtDart34, cdtDart45]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, cdtDart53, cdtDart34, cdtDart45]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaceBoundary,
        cdt35, cdt34, cdt45, cdtDart53, cdtDart34, cdtDart45]
  hface_sub := by
    intro e he
    have he' : e = cdt35 ∨ e = cdt34 ∨ e = cdt45 := by
      simpa [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaceBoundary]
        using he
    rcases he' with rfl | rfl | rfl <;>
      simp [cdt35, cdt34, cdt45, cdtDart53, cdtDart34, cdtDart45]

def chainedDiamondsFace3PureDartCycle
    (hf : (3 : ChainedDiamondsWithTriangleFace) ∈ chainedDiamondsWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      chainedDiamondsWithTriangleEmbedding ⟨(3 : ChainedDiamondsWithTriangleFace), hf⟩ where
  darts := [cdtDart56, cdtDart64, cdtDart45]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, cdtDart56, cdtDart64, cdtDart45]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaceBoundary,
        cdt56, cdt46, cdt45, cdtDart56, cdtDart64, cdtDart45]
  hface_sub := by
    intro e he
    have he' : e = cdt56 ∨ e = cdt46 ∨ e = cdt45 := by
      simpa [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaceBoundary]
        using he
    rcases he' with rfl | rfl | rfl <;>
      simp [cdt56, cdt46, cdt45, cdtDart56, cdtDart64, cdtDart45]

def chainedDiamondsFace4PureDartCycle
    (hf : (4 : ChainedDiamondsWithTriangleFace) ∈ chainedDiamondsWithTriangleEmbedding.faces) :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycle
      chainedDiamondsWithTriangleEmbedding ⟨(4 : ChainedDiamondsWithTriangleFace), hf⟩ where
  darts := [cdtDart78, cdtDart89, cdtDart97]
  hnonempty := by simp
  hclosed := by
    simp [SimpleGraph.DartAdj, cdtDart78, cdtDart89, cdtDart97]
  hnodup_edges := by decide
  hedge_sub := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaceBoundary,
        cdt78, cdt89, cdt97, cdtDart78, cdtDart89, cdtDart97]
  hface_sub := by
    intro e he
    have he' : e = cdt78 ∨ e = cdt89 ∨ e = cdt97 := by
      simpa [chainedDiamondsWithTriangleEmbedding, chainedDiamondsWithTriangleFaceBoundary]
        using he
    rcases he' with rfl | rfl | rfl <;>
      simp [cdt78, cdt89, cdt97, cdtDart78, cdtDart89, cdtDart97]

def chainedDiamondsPureDartCycleGeometry :
    PlaneEmbeddingWithBoundary.FaceBoundaryPureDartCycleGeometry
      chainedDiamondsWithTriangleEmbedding where
  faceBoundaryPureDartCycle := by
    intro f
    rcases f with ⟨f, hfmem⟩
    change ChainedDiamondsWithTriangleFace at f
    by_cases h0 : f = (0 : ChainedDiamondsWithTriangleFace)
    · subst f
      exact chainedDiamondsFace0PureDartCycle hfmem
    · by_cases h1 : f = (1 : ChainedDiamondsWithTriangleFace)
      · subst f
        exact chainedDiamondsFace1PureDartCycle hfmem
      · by_cases h2 : f = (2 : ChainedDiamondsWithTriangleFace)
        · subst f
          exact chainedDiamondsFace2PureDartCycle hfmem
        · by_cases h3 : f = (3 : ChainedDiamondsWithTriangleFace)
          · subst f
            exact chainedDiamondsFace3PureDartCycle hfmem
          · have h4 : f = (4 : ChainedDiamondsWithTriangleFace) := by
              fin_cases f
              · exact False.elim (h0 rfl)
              · exact False.elim (h1 rfl)
              · exact False.elim (h2 rfl)
              · exact False.elim (h3 rfl)
              · rfl
            subst f
            exact chainedDiamondsFace4PureDartCycle hfmem

def chainedDiamondsClosedWalkEmbeddingData :
    PlanarBoundaryClosedWalkEmbeddingData chainedDiamondsWithTriangleEmbedding :=
  chainedDiamondsPureDartCycleGeometry.toFaceBoundaryClosedWalkGeometry

theorem chainedDiamondsClosedWalkEmbeddingData_selectedBoundaryArcOnFace :
    ∀ f : AmbientFace chainedDiamondsWithTriangleEmbedding.faces,
      (chainedDiamondsClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace f := by
  intro f
  have hf_cases :
      f = chainedDiamondsFace0 ∨ f = chainedDiamondsFace1 ∨
        f = chainedDiamondsFace2 ∨ f = chainedDiamondsFace3 ∨
          f = chainedDiamondsFace4 := by
    rcases f with ⟨⟨n, hn⟩, hfmem⟩
    have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
      omega
    rcases hn_cases with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Subtype.ext rfl)
    · exact Or.inr <| Or.inl (Subtype.ext rfl)
    · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext rfl)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext rfl)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr (Subtype.ext rfl)
  rcases hf_cases with rfl | hf_cases
  · change
      (chainedDiamondsClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
        |>.SelectedBoundaryArcOnFace chainedDiamondsFace0
    refine ⟨[cdt02, cdt01], ?_, ?_⟩
    · decide
    · intro e
      rcases chainedDiamondsWithTriangle_edge_eq e with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · rcases hf_cases with rfl | hf_cases
    · change
        (chainedDiamondsClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
          |>.SelectedBoundaryArcOnFace chainedDiamondsFace1
      refine ⟨[cdt23, cdt13], ?_, ?_⟩
      · decide
      · intro e
        rcases chainedDiamondsWithTriangle_edge_eq e with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide
    · rcases hf_cases with rfl | hf_cases
      · change
          (chainedDiamondsClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
            |>.SelectedBoundaryArcOnFace chainedDiamondsFace2
        refine ⟨[cdt35, cdt34], ?_, ?_⟩
        · decide
        · intro e
          rcases chainedDiamondsWithTriangle_edge_eq e with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            decide
      · rcases hf_cases with rfl | rfl
        · change
            (chainedDiamondsClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
              |>.SelectedBoundaryArcOnFace chainedDiamondsFace3
          refine ⟨[cdt56, cdt46], ?_, ?_⟩
          · decide
          · intro e
            rcases chainedDiamondsWithTriangle_edge_eq e with
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              decide
        · change
            (chainedDiamondsClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry)
              |>.SelectedBoundaryArcOnFace chainedDiamondsFace4
          refine ⟨[cdt78, cdt89, cdt97], ?_, ?_⟩
          · decide
          · intro e
            rcases chainedDiamondsWithTriangle_edge_eq e with
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              decide

def chainedDiamondsOuterRoot :
    PlanarBoundaryEdgeVertex chainedDiamondsWithTriangleEmbedding :=
  ⟨cdt01, cdt01_mem_selectedBoundarySupport⟩

def chainedDiamondsInnerRoot :
    PlanarBoundaryEdgeVertex chainedDiamondsWithTriangleEmbedding :=
  ⟨cdt78, cdt78_mem_selectedBoundarySupport⟩

def chainedDiamondsBoundaryLabel
    (e : PlanarBoundaryEdgeVertex chainedDiamondsWithTriangleEmbedding) : Bool :=
  if e.1 = cdt78 ∨ e.1 = cdt89 ∨ e.1 = cdt97 then true else false

theorem chainedDiamonds_boundaryEdge_eq
    (e : PlanarBoundaryEdgeVertex chainedDiamondsWithTriangleEmbedding) :
    e = ⟨cdt01, cdt01_mem_selectedBoundarySupport⟩ ∨
      e = ⟨cdt02, cdt02_mem_selectedBoundarySupport⟩ ∨
      e = ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ ∨
      e = ⟨cdt23, cdt23_mem_selectedBoundarySupport⟩ ∨
      e = ⟨cdt34, cdt34_mem_selectedBoundarySupport⟩ ∨
      e = ⟨cdt35, cdt35_mem_selectedBoundarySupport⟩ ∨
      e = ⟨cdt46, cdt46_mem_selectedBoundarySupport⟩ ∨
      e = ⟨cdt56, cdt56_mem_selectedBoundarySupport⟩ ∨
      e = ⟨cdt78, cdt78_mem_selectedBoundarySupport⟩ ∨
      e = ⟨cdt89, cdt89_mem_selectedBoundarySupport⟩ ∨
      e = ⟨cdt97, cdt97_mem_selectedBoundarySupport⟩ := by
  rcases chainedDiamondsWithTriangle_edge_eq e.1 with
    h01 | h12 | h02 | h13 | h23 | h34 | h45 | h35 | h46 | h56 | h78 | h89 | h97
  · exact Or.inl (Subtype.ext h01)
  · exact False.elim (cdt12_not_mem_selectedBoundarySupport (by simpa [h12] using e.2))
  · exact Or.inr <| Or.inl (Subtype.ext h02)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h13)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h23)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h34)
  · exact False.elim (cdt45_not_mem_selectedBoundarySupport (by simpa [h45] using e.2))
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h35)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h46)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inl (Subtype.ext h56)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inl (Subtype.ext h78)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h89)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      <| Or.inr <| Or.inr <| Or.inr (Subtype.ext h97)

theorem chainedDiamondsBoundaryAdj_preserves_label :
    ∀ ⦃e f : PlanarBoundaryEdgeVertex chainedDiamondsWithTriangleEmbedding⦄,
      (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj e f →
        chainedDiamondsBoundaryLabel e = chainedDiamondsBoundaryLabel f := by
  intro e f hadj
  rcases chainedDiamonds_boundaryEdge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases chainedDiamonds_boundaryEdge_eq f with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact False.elim
          (by
            rcases hadj with ⟨_, v, hvE, hvF⟩
            fin_cases v <;>
              simp [cdt01, cdt02, cdt13, cdt23, cdt34, cdt35, cdt46, cdt56,
                cdt78, cdt89, cdt97] at hvE hvF)

theorem chainedDiamondsOuterRoot_ne_innerRoot :
    chainedDiamondsOuterRoot ≠ chainedDiamondsInnerRoot := by
  intro h
  have := congrArg Subtype.val h
  simp [chainedDiamondsOuterRoot, chainedDiamondsInnerRoot, cdt01, cdt78] at this

def chainedDiamondsAnnulusBoundaryReachabilityData :
    PlanarBoundaryAnnulusBoundaryReachabilityData chainedDiamondsWithTriangleEmbedding where
  outerRoot := chainedDiamondsOuterRoot
  innerRoot := chainedDiamondsInnerRoot
  hroots_ne := chainedDiamondsOuterRoot_ne_innerRoot
  hcoverRoots := by
    intro e
    rcases chainedDiamonds_boundaryEdge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨chainedDiamondsOuterRoot, by simp [chainedDiamondsOuterRoot_ne_innerRoot],
        SimpleGraph.Reachable.refl _⟩
    · refine ⟨chainedDiamondsOuterRoot, by simp [chainedDiamondsOuterRoot_ne_innerRoot],
        ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
            ⟨cdt02, cdt02_mem_selectedBoundarySupport⟩ chainedDiamondsOuterRoot := by
        refine ⟨?_, 0, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [chainedDiamondsOuterRoot, cdt02, cdt01] at this
        · simp [cdt02]
        · simp [chainedDiamondsOuterRoot, cdt01]
      exact hadj.reachable
    · refine ⟨chainedDiamondsOuterRoot, by simp [chainedDiamondsOuterRoot_ne_innerRoot],
        ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
            ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ chainedDiamondsOuterRoot := by
        refine ⟨?_, 1, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [chainedDiamondsOuterRoot, cdt13, cdt01] at this
        · simp [cdt13]
        · simp [chainedDiamondsOuterRoot, cdt01]
      exact hadj.reachable
    · refine ⟨chainedDiamondsOuterRoot, by simp [chainedDiamondsOuterRoot_ne_innerRoot],
        ?_⟩
      have h23_13 :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Reachable
            ⟨cdt23, cdt23_mem_selectedBoundarySupport⟩
            ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
              ⟨cdt23, cdt23_mem_selectedBoundarySupport⟩
              ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ := by
          refine ⟨?_, 3, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [cdt23, cdt13] at this
          · simp [cdt23]
          · simp [cdt13]
        exact hadj.reachable
      have h13_outer :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Reachable
            ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ chainedDiamondsOuterRoot := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
              ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ chainedDiamondsOuterRoot := by
          refine ⟨?_, 1, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [chainedDiamondsOuterRoot, cdt13, cdt01] at this
          · simp [cdt13]
          · simp [chainedDiamondsOuterRoot, cdt01]
        exact hadj.reachable
      exact h23_13.trans h13_outer
    · refine ⟨chainedDiamondsOuterRoot, by simp [chainedDiamondsOuterRoot_ne_innerRoot],
        ?_⟩
      have h34_13 :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Reachable
            ⟨cdt34, cdt34_mem_selectedBoundarySupport⟩
            ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
              ⟨cdt34, cdt34_mem_selectedBoundarySupport⟩
              ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ := by
          refine ⟨?_, 3, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [cdt34, cdt13] at this
          · simp [cdt34]
          · simp [cdt13]
        exact hadj.reachable
      have h13_outer :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Reachable
            ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ chainedDiamondsOuterRoot := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
              ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ chainedDiamondsOuterRoot := by
          refine ⟨?_, 1, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [chainedDiamondsOuterRoot, cdt13, cdt01] at this
          · simp [cdt13]
          · simp [chainedDiamondsOuterRoot, cdt01]
        exact hadj.reachable
      exact h34_13.trans h13_outer
    · refine ⟨chainedDiamondsOuterRoot, by simp [chainedDiamondsOuterRoot_ne_innerRoot],
        ?_⟩
      have h35_13 :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Reachable
            ⟨cdt35, cdt35_mem_selectedBoundarySupport⟩
            ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
              ⟨cdt35, cdt35_mem_selectedBoundarySupport⟩
              ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ := by
          refine ⟨?_, 3, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [cdt35, cdt13] at this
          · simp [cdt35]
          · simp [cdt13]
        exact hadj.reachable
      have h13_outer :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Reachable
            ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ chainedDiamondsOuterRoot := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
              ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ chainedDiamondsOuterRoot := by
          refine ⟨?_, 1, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [chainedDiamondsOuterRoot, cdt13, cdt01] at this
          · simp [cdt13]
          · simp [chainedDiamondsOuterRoot, cdt01]
        exact hadj.reachable
      exact h35_13.trans h13_outer
    · refine ⟨chainedDiamondsOuterRoot, by simp [chainedDiamondsOuterRoot_ne_innerRoot],
        ?_⟩
      have h46_34 :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Reachable
            ⟨cdt46, cdt46_mem_selectedBoundarySupport⟩
            ⟨cdt34, cdt34_mem_selectedBoundarySupport⟩ := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
              ⟨cdt46, cdt46_mem_selectedBoundarySupport⟩
              ⟨cdt34, cdt34_mem_selectedBoundarySupport⟩ := by
          refine ⟨?_, 4, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [cdt46, cdt34] at this
          · simp [cdt46]
          · simp [cdt34]
        exact hadj.reachable
      have h34_13 :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Reachable
            ⟨cdt34, cdt34_mem_selectedBoundarySupport⟩
            ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
              ⟨cdt34, cdt34_mem_selectedBoundarySupport⟩
              ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ := by
          refine ⟨?_, 3, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [cdt34, cdt13] at this
          · simp [cdt34]
          · simp [cdt13]
        exact hadj.reachable
      have h13_outer :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Reachable
            ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ chainedDiamondsOuterRoot := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
              ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ chainedDiamondsOuterRoot := by
          refine ⟨?_, 1, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [chainedDiamondsOuterRoot, cdt13, cdt01] at this
          · simp [cdt13]
          · simp [chainedDiamondsOuterRoot, cdt01]
        exact hadj.reachable
      exact h46_34.trans (h34_13.trans h13_outer)
    · refine ⟨chainedDiamondsOuterRoot, by simp [chainedDiamondsOuterRoot_ne_innerRoot],
        ?_⟩
      have h56_35 :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Reachable
            ⟨cdt56, cdt56_mem_selectedBoundarySupport⟩
            ⟨cdt35, cdt35_mem_selectedBoundarySupport⟩ := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
              ⟨cdt56, cdt56_mem_selectedBoundarySupport⟩
              ⟨cdt35, cdt35_mem_selectedBoundarySupport⟩ := by
          refine ⟨?_, 5, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [cdt56, cdt35] at this
          · simp [cdt56]
          · simp [cdt35]
        exact hadj.reachable
      have h35_13 :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Reachable
            ⟨cdt35, cdt35_mem_selectedBoundarySupport⟩
            ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
              ⟨cdt35, cdt35_mem_selectedBoundarySupport⟩
              ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ := by
          refine ⟨?_, 3, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [cdt35, cdt13] at this
          · simp [cdt35]
          · simp [cdt13]
        exact hadj.reachable
      have h13_outer :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Reachable
            ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ chainedDiamondsOuterRoot := by
        have hadj :
            (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
              ⟨cdt13, cdt13_mem_selectedBoundarySupport⟩ chainedDiamondsOuterRoot := by
          refine ⟨?_, 1, ?_, ?_⟩
          · intro h
            have := congrArg Subtype.val h
            simp [chainedDiamondsOuterRoot, cdt13, cdt01] at this
          · simp [cdt13]
          · simp [chainedDiamondsOuterRoot, cdt01]
        exact hadj.reachable
      exact h56_35.trans (h35_13.trans h13_outer)
    · refine ⟨chainedDiamondsInnerRoot, by simp, SimpleGraph.Reachable.refl _⟩
    · refine ⟨chainedDiamondsInnerRoot, by simp, ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
            ⟨cdt89, cdt89_mem_selectedBoundarySupport⟩ chainedDiamondsInnerRoot := by
        refine ⟨?_, 8, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [chainedDiamondsInnerRoot, cdt89, cdt78] at this
        · simp [cdt89]
        · simp [chainedDiamondsInnerRoot, cdt78]
      exact hadj.reachable
    · refine ⟨chainedDiamondsInnerRoot, by simp, ?_⟩
      have hadj :
          (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding).Adj
            ⟨cdt97, cdt97_mem_selectedBoundarySupport⟩ chainedDiamondsInnerRoot := by
        refine ⟨?_, 7, ?_, ?_⟩
        · intro h
          have := congrArg Subtype.val h
          simp [chainedDiamondsInnerRoot, cdt97, cdt78] at this
        · simp [cdt97]
        · simp [chainedDiamondsInnerRoot, cdt78]
      exact hadj.reachable
  hsepRoots := by
    intro r s hr hs hreach
    have hlabelEq :
        chainedDiamondsBoundaryLabel r = chainedDiamondsBoundaryLabel s :=
      eq_of_reachable_of_eq_on_adj
        (planarBoundarySupportEndpointAdjGraph chainedDiamondsWithTriangleEmbedding)
        chainedDiamondsBoundaryLabel
        (by
          intro u v huv
          exact chainedDiamondsBoundaryAdj_preserves_label huv)
        hreach
    have hOuterLabel : chainedDiamondsBoundaryLabel chainedDiamondsOuterRoot = false := by
      decide
    have hInnerLabel : chainedDiamondsBoundaryLabel chainedDiamondsInnerRoot = true := by
      decide
    have hr_cases : r = chainedDiamondsOuterRoot ∨ r = chainedDiamondsInnerRoot := by
      simpa [chainedDiamondsOuterRoot_ne_innerRoot] using hr
    have hs_cases : s = chainedDiamondsOuterRoot ∨ s = chainedDiamondsInnerRoot := by
      simpa [chainedDiamondsOuterRoot_ne_innerRoot] using hs
    rcases hr_cases with rfl | rfl <;> rcases hs_cases with rfl | rfl
    · rfl
    · rw [hOuterLabel, hInnerLabel] at hlabelEq
      cases hlabelEq
    · rw [hInnerLabel, hOuterLabel] at hlabelEq
      cases hlabelEq
    · rfl

def chainedDiamondsClosedWalkAnnulusBoundarySource :
    PlanarBoundaryClosedWalkAnnulusBoundarySource chainedDiamondsWithTriangleEmbedding :=
  PlanarBoundaryClosedWalkAnnulusBoundarySource.ofFields
    chainedDiamondsAnnulusBoundaryReachabilityData
    chainedDiamondsClosedWalkEmbeddingData
    chainedDiamondsClosedWalkEmbeddingData_selectedBoundaryArcOnFace

def chainedDiamondsCanonicalWitnessEdge :
    AmbientFace chainedDiamondsWithTriangleEmbedding.faces →
      chainedDiamondsWithTriangleGraph.edgeSet
  | ⟨⟨0, _⟩, _⟩ => cdt12
  | ⟨⟨1, _⟩, _⟩ => cdt12
  | ⟨⟨2, _⟩, _⟩ => cdt45
  | ⟨⟨3, _⟩, _⟩ => cdt45
  | ⟨⟨4, _⟩, _⟩ => cdt78

/-- Concrete canonical witness choice on the chained-two-diamond honest source.  The two
diamond cells choose their respective shared interior edges, while the inner triangle chooses a
boundary edge; every remaining face-boundary edge is then selected boundary and hence belongs to
one of the two ambient annulus boundary components extracted from the honest source. -/
noncomputable def chainedDiamondsClosedWalkCanonicalWitnessChoice :
    PlanarBoundaryCanonicalWitnessChoice
      chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData := by
  classical
  refine
    { witnessEdge := chainedDiamondsCanonicalWitnessEdge
      hcover := by decide
      hwitness := by decide
      hrest := ?_ }
  intro f e he
  have heSelected :
      e ∈ selectedBoundarySupport chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
    rcases chainedDiamondsWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cdt01_mem_selectedBoundarySupport
    · exfalso
      fin_cases f <;>
        simp [chainedDiamondsCanonicalWitnessEdge, chainedDiamondsWithTriangleEmbedding,
          chainedDiamondsWithTriangleFaceBoundary, cdt01, cdt12, cdt02, cdt13, cdt23,
          cdt34, cdt45, cdt35, cdt46, cdt56, cdt78, cdt89, cdt97] at he
    · exact cdt02_mem_selectedBoundarySupport
    · exact cdt13_mem_selectedBoundarySupport
    · exact cdt23_mem_selectedBoundarySupport
    · exact cdt34_mem_selectedBoundarySupport
    · exfalso
      fin_cases f <;>
        simp [chainedDiamondsCanonicalWitnessEdge, chainedDiamondsWithTriangleEmbedding,
          chainedDiamondsWithTriangleFaceBoundary, cdt01, cdt12, cdt02, cdt13, cdt23,
          cdt34, cdt45, cdt35, cdt46, cdt56, cdt78, cdt89, cdt97] at he
    · exact cdt35_mem_selectedBoundarySupport
    · exact cdt46_mem_selectedBoundarySupport
    · exact cdt56_mem_selectedBoundarySupport
    · exact cdt78_mem_selectedBoundarySupport
    · exact cdt89_mem_selectedBoundarySupport
    · exact cdt97_mem_selectedBoundarySupport
  exact
    chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData
      |>.hambientBoundaryCover heSelected

/-- The interior edge support of the chained diamonds model consists of exactly the two
diamond-interior edges `cdt12` and `cdt45`. -/
theorem chainedDiamondsWithTriangle_interiorEdgeSupport_eq :
    interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
      chainedDiamondsWithTriangleEmbedding.faces = {cdt12, cdt45} := by
  ext e
  constructor
  · intro he
    rw [mem_interiorEdgeSupport_iff] at he
    rcases chainedDiamondsWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have : totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
          chainedDiamondsWithTriangleFaces cdt01 = 1 := totalIncidenceCount_cdt01
      simp [chainedDiamondsWithTriangleEmbedding] at he
      omega
    · simp
    · have : totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
          chainedDiamondsWithTriangleFaces cdt02 = 1 := totalIncidenceCount_cdt02
      simp [chainedDiamondsWithTriangleEmbedding] at he
      omega
    · have : totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
          chainedDiamondsWithTriangleFaces cdt13 = 1 := totalIncidenceCount_cdt13
      simp [chainedDiamondsWithTriangleEmbedding] at he
      omega
    · have : totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
          chainedDiamondsWithTriangleFaces cdt23 = 1 := totalIncidenceCount_cdt23
      simp [chainedDiamondsWithTriangleEmbedding] at he
      omega
    · have : totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
          chainedDiamondsWithTriangleFaces cdt34 = 1 := totalIncidenceCount_cdt34
      simp [chainedDiamondsWithTriangleEmbedding] at he
      omega
    · simp
    · have : totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
          chainedDiamondsWithTriangleFaces cdt35 = 1 := totalIncidenceCount_cdt35
      simp [chainedDiamondsWithTriangleEmbedding] at he
      omega
    · have : totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
          chainedDiamondsWithTriangleFaces cdt46 = 1 := totalIncidenceCount_cdt46
      simp [chainedDiamondsWithTriangleEmbedding] at he
      omega
    · have : totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
          chainedDiamondsWithTriangleFaces cdt56 = 1 := totalIncidenceCount_cdt56
      simp [chainedDiamondsWithTriangleEmbedding] at he
      omega
    · have : totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
          chainedDiamondsWithTriangleFaces cdt78 = 1 := totalIncidenceCount_cdt78
      simp [chainedDiamondsWithTriangleEmbedding] at he
      omega
    · have : totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
          chainedDiamondsWithTriangleFaces cdt89 = 1 := totalIncidenceCount_cdt89
      simp [chainedDiamondsWithTriangleEmbedding] at he
      omega
    · have : totalIncidenceCount chainedDiamondsWithTriangleFaceBoundary
          chainedDiamondsWithTriangleFaces cdt97 = 1 := totalIncidenceCount_cdt97
      simp [chainedDiamondsWithTriangleEmbedding] at he
      omega
  · intro he
    simp at he
    rcases he with rfl | rfl
    · exact cdt12_mem_interiorEdgeSupport
    · exact cdt45_mem_interiorEdgeSupport

/-- Each face in the chained diamonds model has at most one interior edge on its boundary. -/
theorem chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace :
    ∀ f : AmbientFace chainedDiamondsWithTriangleEmbedding.faces,
      ((chainedDiamondsWithTriangleEmbedding.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
            chainedDiamondsWithTriangleEmbedding.faces)).card ≤ 1 := by
  intro f
  have hsupp := chainedDiamondsWithTriangle_interiorEdgeSupport_eq
  -- Each face boundary filters to at most a singleton from {cdt12, cdt45}
  obtain ⟨⟨i, hi⟩, hf⟩ := f
  interval_cases i
  · -- Face 0: {cdt02, cdt01, cdt12} ∩ {cdt12, cdt45} = {cdt12}
    show (Finset.filter (fun x => x ∈ ({cdt12, cdt45} : Finset _))
      ({cdt02, cdt01, cdt12} : Finset _)).card ≤ 1
    decide
  · -- Face 1: {cdt23, cdt13, cdt12} ∩ {cdt12, cdt45} = {cdt12}
    show (Finset.filter (fun x => x ∈ ({cdt12, cdt45} : Finset _))
      ({cdt23, cdt13, cdt12} : Finset _)).card ≤ 1
    decide
  · -- Face 2: {cdt35, cdt34, cdt45} ∩ {cdt12, cdt45} = {cdt45}
    show (Finset.filter (fun x => x ∈ ({cdt12, cdt45} : Finset _))
      ({cdt35, cdt34, cdt45} : Finset _)).card ≤ 1
    decide
  · -- Face 3: {cdt56, cdt46, cdt45} ∩ {cdt12, cdt45} = {cdt45}
    show (Finset.filter (fun x => x ∈ ({cdt12, cdt45} : Finset _))
      ({cdt56, cdt46, cdt45} : Finset _)).card ≤ 1
    decide
  · -- Face 4: {cdt78, cdt89, cdt97} ∩ {cdt12, cdt45} = {}
    show (Finset.filter (fun x => x ∈ ({cdt12, cdt45} : Finset _))
      ({cdt78, cdt89, cdt97} : Finset _)).card ≤ 1
    decide

/-- The larger chained-diamonds at-most-one benchmark still has empty purified
selected-boundary interior carrier: every endpoint of its two interior edges is incident to a
selected boundary edge. -/
theorem selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_chainedDiamondsWithTriangle :
    selectedBoundaryInteriorEdgeEndpointVertices chainedDiamondsWithTriangleEmbedding = ∅ := by
  ext v
  constructor
  · intro hv
    rcases
      (mem_selectedBoundaryInteriorEdgeEndpointVertices_iff
        chainedDiamondsWithTriangleEmbedding).1 hv with
      ⟨⟨e, heInterior, hve⟩, havoid⟩
    have heCases : e = cdt12 ∨ e = cdt45 := by
      have hmem : e ∈ ({cdt12, cdt45} : Finset _) := by
        simpa [chainedDiamondsWithTriangle_interiorEdgeSupport_eq] using heInterior
      simpa using hmem
    rcases heCases with rfl | rfl
    · have hvCases : v = (1 : Fin 10) ∨ v = (2 : Fin 10) := by
        simpa [cdt12, Sym2.mem_iff] using hve
      rcases hvCases with rfl | rfl
      · exfalso
        exact (havoid cdt01 cdt01_mem_selectedBoundarySupport) (by simp [cdt01])
      · exfalso
        exact (havoid cdt02 cdt02_mem_selectedBoundarySupport) (by simp [cdt02])
    · have hvCases : v = (4 : Fin 10) ∨ v = (5 : Fin 10) := by
        simpa [cdt45, Sym2.mem_iff] using hve
      rcases hvCases with rfl | rfl
      · exfalso
        exact (havoid cdt34 cdt34_mem_selectedBoundarySupport) (by simp [cdt34])
      · exfalso
        exact (havoid cdt35 cdt35_mem_selectedBoundarySupport) (by simp [cdt35])
  · intro hv
    simp at hv

theorem not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_chainedDiamondsWithTriangle :
    ¬ (selectedBoundaryInteriorEdgeEndpointVertices
        chainedDiamondsWithTriangleEmbedding).Nonempty := by
  intro hv
  simp [selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_chainedDiamondsWithTriangle] at hv

theorem chainedDiamondsClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice :
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) := by
  exact ⟨chainedDiamondsClosedWalkCanonicalWitnessChoice⟩

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_chainedDiamondsWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    ⟨chainedDiamondsWithTriangleEmbedding, chainedDiamondsClosedWalkAnnulusBoundarySource,
      chainedDiamondsClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice⟩

theorem
    chainedDiamondsWithTriangleGraph_admitsPlanarBoundaryAnnulusWitnessAssignment_via_closedWalkCanonicalWitnessChoice :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment chainedDiamondsWithTriangleGraph := by
  exact
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_planarBoundaryCanonicalWitnessChoice
      ⟨chainedDiamondsWithTriangleEmbedding,
        chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData,
        chainedDiamondsClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice⟩

noncomputable def chainedDiamondsOneCollarGeometry :
    PlanarBoundaryAnnulusCollarGeometry chainedDiamondsWithTriangleEmbedding :=
  chainedDiamondsClosedWalkCanonicalWitnessChoice.toPlanarBoundaryAnnulusCollarGeometry

theorem chainedDiamondsOneCollarGeometry_numCollars :
    chainedDiamondsOneCollarGeometry.numCollars = 1 := by
  rfl

theorem chainedDiamondsOneCollarGeometry_boundaryData :
    chainedDiamondsOneCollarGeometry.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
      chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData := by
  rfl

theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCollarGeometry_chainedDiamondsWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusDecomposition.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData := by
  exact
    ⟨chainedDiamondsWithTriangleEmbedding, chainedDiamondsClosedWalkAnnulusBoundarySource,
      chainedDiamondsOneCollarGeometry, chainedDiamondsOneCollarGeometry_numCollars,
      chainedDiamondsOneCollarGeometry_boundaryData⟩

theorem
    chainedDiamondsWithTriangleGraph_admitsPlanarBoundaryAnnulusCollarGeometry_via_closedWalkCanonicalWitnessChoice :
    AdmitsPlanarBoundaryAnnulusCollarGeometry chainedDiamondsWithTriangleGraph := by
  exact ⟨chainedDiamondsWithTriangleEmbedding, ⟨chainedDiamondsOneCollarGeometry⟩⟩

noncomputable def chainedDiamondsOneCollarPreviousBoundaryWitnessGeometry :
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry chainedDiamondsWithTriangleEmbedding := by
  refine
    { toPlanarBoundaryAnnulusCollarGeometry := chainedDiamondsOneCollarGeometry
      hwitnessPrev := ?_ }
  intro j g hgj hjpos
  fin_cases j
  exact False.elim (Nat.lt_irrefl 0 hjpos)

theorem chainedDiamondsOneCollarWitnessOnCurrentBoundary :
    chainedDiamondsOneCollarGeometry.WitnessOnCurrentBoundary := by
  intro j g hgj hjpos
  fin_cases j
  exact False.elim (Nat.lt_irrefl 0 hjpos)

theorem
    chainedDiamondsWithTriangleGraph_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry_via_closedWalkCanonicalWitnessChoice :
    AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry chainedDiamondsWithTriangleGraph := by
  exact
    ⟨chainedDiamondsWithTriangleEmbedding,
      ⟨chainedDiamondsOneCollarPreviousBoundaryWitnessGeometry⟩⟩

noncomputable def chainedDiamondsOneCollarCollarLayerFacePeelWitnessData :
    PlanarBoundaryCollarLayerFacePeelWitnessData chainedDiamondsWithTriangleEmbedding :=
  chainedDiamondsOneCollarGeometry.toPlanarBoundaryCollarLayerFacePeelWitnessData

theorem chainedDiamondsOneCollarGeometry_hasCollarLayerFacePeelWitnessData :
    Nonempty
      (PlanarBoundaryCollarLayerFacePeelWitnessData chainedDiamondsWithTriangleEmbedding) := by
  exact ⟨chainedDiamondsOneCollarCollarLayerFacePeelWitnessData⟩

theorem
    chainedDiamondsWithTriangleGraph_admitsPlanarBoundaryCollarLayerFacePeelWitnessData_via_oneCollarGeometry :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData chainedDiamondsWithTriangleGraph := by
  exact
    ⟨chainedDiamondsWithTriangleEmbedding,
      ⟨chainedDiamondsOneCollarCollarLayerFacePeelWitnessData⟩⟩

noncomputable def chainedDiamondsOneCollarHeightOrderedFacePeelWitnessData :
    PlanarBoundaryHeightOrderedFacePeelWitnessData chainedDiamondsWithTriangleEmbedding :=
  chainedDiamondsOneCollarGeometry.toPlanarBoundaryHeightOrderedFacePeelWitnessData

theorem chainedDiamondsOneCollarGeometry_hasHeightOrderedFacePeelWitnessData :
    Nonempty
      (PlanarBoundaryHeightOrderedFacePeelWitnessData chainedDiamondsWithTriangleEmbedding) := by
  exact ⟨chainedDiamondsOneCollarHeightOrderedFacePeelWitnessData⟩

theorem
    chainedDiamondsWithTriangleGraph_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_via_oneCollarGeometry :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData chainedDiamondsWithTriangleGraph := by
  exact
    ⟨chainedDiamondsWithTriangleEmbedding,
      ⟨chainedDiamondsOneCollarHeightOrderedFacePeelWitnessData⟩⟩

noncomputable def chainedDiamondsOneCollarWellFoundedFacePeelWitnessData :
    PlanarBoundaryWellFoundedFacePeelWitnessData chainedDiamondsWithTriangleEmbedding :=
  chainedDiamondsOneCollarPreviousBoundaryWitnessGeometry.toPlanarBoundaryWellFoundedFacePeelWitnessData

theorem chainedDiamondsOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData :
    Nonempty
      (PlanarBoundaryWellFoundedFacePeelWitnessData chainedDiamondsWithTriangleEmbedding) := by
  exact ⟨chainedDiamondsOneCollarWellFoundedFacePeelWitnessData⟩

theorem
    chainedDiamondsWithTriangleGraph_admitsPlanarBoundaryWellFoundedFacePeelWitnessData_via_oneCollarGeometry :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData chainedDiamondsWithTriangleGraph := by
  exact
    ⟨chainedDiamondsWithTriangleEmbedding,
      ⟨chainedDiamondsOneCollarWellFoundedFacePeelWitnessData⟩⟩

noncomputable def chainedDiamondsOneCollarAttachedRootedFacePeelCertificate :
    PlanarBoundaryAttachedRootedFacePeelCertificate chainedDiamondsWithTriangleGraph :=
  chainedDiamondsOneCollarGeometry.toPlanarBoundaryAttachedRootedFacePeelCertificate

theorem chainedDiamondsOneCollarGeometry_hasAttachedRootedFacePeelCertificate :
    Nonempty
      (BoundaryRootedFacePeelCertificate chainedDiamondsWithTriangleEmbedding.faces.attach
        (ambientFaceBoundary (allFaces := chainedDiamondsWithTriangleEmbedding.faces)
          chainedDiamondsWithTriangleEmbedding.faceBoundary)) := by
  exact ⟨chainedDiamondsOneCollarAttachedRootedFacePeelCertificate.certificate⟩

theorem
    chainedDiamondsWithTriangleGraph_admitsPlanarBoundaryAttachedRootedFacePeelCertificate_via_oneCollarGeometry :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate chainedDiamondsWithTriangleGraph := by
  exact ⟨chainedDiamondsOneCollarAttachedRootedFacePeelCertificate⟩

theorem
    closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_chainedDiamondsWithTriangle :
    Nonempty
        (PlanarBoundaryClosedWalkAnnulusBoundarySource chainedDiamondsWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry chainedDiamondsWithTriangleEmbedding) ∧
        Nonempty
          (BoundaryRootedFacePeelCertificate chainedDiamondsWithTriangleEmbedding.faces.attach
            (ambientFaceBoundary (allFaces := chainedDiamondsWithTriangleEmbedding.faces)
              chainedDiamondsWithTriangleEmbedding.faceBoundary)) := by
  exact
    ⟨⟨chainedDiamondsClosedWalkAnnulusBoundarySource⟩,
      ⟨chainedDiamondsOneCollarGeometry⟩,
      chainedDiamondsOneCollarGeometry_hasAttachedRootedFacePeelCertificate⟩

theorem chainedDiamondsWithTriangleEmbedding_theorem49BoundaryRootSynthesis_via_oneCollarGeometry
    [Fintype chainedDiamondsWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (chainedDiamondsWithTriangleGraph.edgeSet → Color)]
    (C₀ : chainedDiamondsWithTriangleGraph.EdgeColoring Color)
    (hC₀ : IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C₀) :
    Theorem49BoundaryRootSynthesis chainedDiamondsWithTriangleEmbedding C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusCollarGeometry
      (G := chainedDiamondsWithTriangleGraph) chainedDiamondsOneCollarGeometry C₀ hC₀

theorem
    exists_theorem49BoundaryRootSynthesis_chainedDiamondsWithTriangleGraph_via_oneCollarGeometry
    [Fintype chainedDiamondsWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (chainedDiamondsWithTriangleGraph.edgeSet → Color)]
    (C₀ : chainedDiamondsWithTriangleGraph.EdgeColoring Color)
    (hC₀ : IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    ⟨chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleEmbedding_theorem49BoundaryRootSynthesis_via_oneCollarGeometry
        C₀ hC₀⟩

theorem chainedDiamondsLineGraphAdj_of_common_vertex_three
    (e f : chainedDiamondsWithTriangleGraph.edgeSet) (hne : e ≠ f)
    (he : (3 : Fin 10) ∈ (e : Sym2 (Fin 10)))
    (hf : (3 : Fin 10) ∈ (f : Sym2 (Fin 10))) :
    (chainedDiamondsWithTriangleGraph.lineGraph).Adj e f := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  exact ⟨hne, ⟨3, he, hf⟩⟩

theorem not_exists_taitEdgeColoring_chainedDiamondsWithTriangleGraph :
    ¬ ∃ C : chainedDiamondsWithTriangleGraph.EdgeColoring Color,
      IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C := by
  rintro ⟨C, hC⟩
  have h13v : (3 : Fin 10) ∈ (cdt13 : Sym2 (Fin 10)) := by simp [cdt13]
  have h23v : (3 : Fin 10) ∈ (cdt23 : Sym2 (Fin 10)) := by simp [cdt23]
  have h34v : (3 : Fin 10) ∈ (cdt34 : Sym2 (Fin 10)) := by simp [cdt34]
  have h35v : (3 : Fin 10) ∈ (cdt35 : Sym2 (Fin 10)) := by simp [cdt35]
  have h13_23 : C cdt13 ≠ C cdt23 :=
    C.valid
      (chainedDiamondsLineGraphAdj_of_common_vertex_three cdt13 cdt23
        (by intro h; simpa [cdt13, cdt23] using congrArg Subtype.val h) h13v h23v)
  have h13_34 : C cdt13 ≠ C cdt34 :=
    C.valid
      (chainedDiamondsLineGraphAdj_of_common_vertex_three cdt13 cdt34
        (by intro h; simpa [cdt13, cdt34] using congrArg Subtype.val h) h13v h34v)
  have h13_35 : C cdt13 ≠ C cdt35 :=
    C.valid
      (chainedDiamondsLineGraphAdj_of_common_vertex_three cdt13 cdt35
        (by intro h; simpa [cdt13, cdt35] using congrArg Subtype.val h) h13v h35v)
  have h23_34 : C cdt23 ≠ C cdt34 :=
    C.valid
      (chainedDiamondsLineGraphAdj_of_common_vertex_three cdt23 cdt34
        (by intro h; simpa [cdt23, cdt34] using congrArg Subtype.val h) h23v h34v)
  have h23_35 : C cdt23 ≠ C cdt35 :=
    C.valid
      (chainedDiamondsLineGraphAdj_of_common_vertex_three cdt23 cdt35
        (by intro h; simpa [cdt23, cdt35] using congrArg Subtype.val h) h23v h35v)
  have h34_35 : C cdt34 ≠ C cdt35 :=
    C.valid
      (chainedDiamondsLineGraphAdj_of_common_vertex_three cdt34 cdt35
        (by intro h; simpa [cdt34, cdt35] using congrArg Subtype.val h) h34v h35v)
  exact
    false_of_four_pairwise_distinct_nonzero_colors (hC cdt13) (hC cdt23) (hC cdt34)
      (hC cdt35) h13_23 h13_34 h13_35 h23_34 h23_35 h34_35

def diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry :
    PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry diamondWithTriangleEmbedding := by
  refine
    { toPlanarBoundaryAnnulusCollarGeometry := diamondWithTriangleOneCollarGeometry
      hwitnessPrev := ?_ }
  intro j g hgj hjpos
  fin_cases j
  exact False.elim (Nat.lt_irrefl 0 hjpos)

theorem diamondWithTriangleOneCollarWitnessOnCurrentBoundary :
    diamondWithTriangleOneCollarGeometry.WitnessOnCurrentBoundary := by
  intro j g hgj hjpos
  fin_cases j
  exact False.elim (Nat.lt_irrefl 0 hjpos)

theorem diamondWithTriangleGraph_admitsPlanarBoundaryAnnulusCollarGeometry :
    AdmitsPlanarBoundaryAnnulusCollarGeometry diamondWithTriangleGraph := by
  exact ⟨diamondWithTriangleEmbedding, ⟨diamondWithTriangleOneCollarGeometry⟩⟩

theorem diamondWithTriangleGraph_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry :
    AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry diamondWithTriangleGraph := by
  exact ⟨diamondWithTriangleEmbedding, ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩⟩

noncomputable def diamondWithTriangleOneCollarWellFoundedFacePeelWitnessData :
    PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding :=
  PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry.toPlanarBoundaryWellFoundedFacePeelWitnessData
    diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry

theorem diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData :
    Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) := by
  exact ⟨diamondWithTriangleOneCollarWellFoundedFacePeelWitnessData⟩

theorem diamondWithTriangleGraph_admitsPlanarBoundaryWellFoundedFacePeelWitnessData_via_oneCollarGeometry :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleGraph := by
  exact ⟨diamondWithTriangleEmbedding, ⟨diamondWithTriangleOneCollarWellFoundedFacePeelWitnessData⟩⟩

noncomputable def diamondWithTriangleOneCollarLayerFacePeelWitnessData :
    PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding :=
  planarBoundaryCollarLayerFacePeelWitnessData_of_genericLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    diamondWithTriangleOneCollarGeometry.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData

theorem diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasCollarLayerFacePeelWitnessData :
    Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) := by
  exact ⟨diamondWithTriangleOneCollarLayerFacePeelWitnessData⟩

theorem diamondWithTriangleGraph_admitsPlanarBoundaryCollarLayerFacePeelWitnessData_via_oneCollarGeometry :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleGraph := by
  exact ⟨diamondWithTriangleEmbedding, ⟨diamondWithTriangleOneCollarLayerFacePeelWitnessData⟩⟩

noncomputable def diamondWithTriangleOneCollarHeightOrderedFacePeelWitnessData :
    PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding :=
  diamondWithTriangleOneCollarLayerFacePeelWitnessData.toHeightOrderedFacePeelWitnessData

theorem diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData :
    Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) := by
  exact ⟨diamondWithTriangleOneCollarHeightOrderedFacePeelWitnessData⟩

theorem diamondWithTriangleGraph_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData_via_oneCollarGeometry :
    AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleGraph := by
  exact ⟨diamondWithTriangleEmbedding, ⟨diamondWithTriangleOneCollarHeightOrderedFacePeelWitnessData⟩⟩

noncomputable def diamondWithTriangleOneCollarConstruction :
    PlanarBoundaryAnnulusConstruction diamondWithTriangleEmbedding :=
  planarBoundaryAnnulusConstruction_of_annulusCollarGeometry diamondWithTriangleOneCollarGeometry

theorem diamondWithTriangleFace0_mem_oneCollarConstruction_peelFaces :
    diamondWithTriangleFace0 ∈ diamondWithTriangleOneCollarConstruction.peelFaces := by
  decide

theorem diamondWithTriangleOneCollarConstruction_faceDistance_face0 :
    diamondWithTriangleOneCollarConstruction.faceDistance diamondWithTriangleFace0 = 0 := by
  rfl

theorem not_diamondWithTriangleOneCollarConstructionParentWitnessOrientation :
    ¬ diamondWithTriangleOneCollarConstruction.ParentWitnessOrientation := by
  intro horient
  rcases horient diamondWithTriangleFace0
      diamondWithTriangleFace0_mem_oneCollarConstruction_peelFaces with ⟨p, _hp, hlt⟩
  rw [diamondWithTriangleOneCollarConstruction_faceDistance_face0] at hlt
  exact (Nat.not_lt_zero _ hlt).elim

noncomputable def diamondWithTriangleOneCollarAttachedRootedFacePeelCertificate :
    PlanarBoundaryAttachedRootedFacePeelCertificate diamondWithTriangleGraph :=
  diamondWithTriangleOneCollarGeometry.toPlanarBoundaryAttachedRootedFacePeelCertificate

theorem diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate :
    Nonempty
      (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
        (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
          diamondWithTriangleEmbedding.faceBoundary)) := by
  exact ⟨diamondWithTriangleOneCollarAttachedRootedFacePeelCertificate.certificate⟩

theorem diamondWithTriangleGraph_admitsPlanarBoundaryAttachedRootedFacePeelCertificate_via_oneCollarGeometry :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate diamondWithTriangleGraph := by
  exact ⟨diamondWithTriangleOneCollarAttachedRootedFacePeelCertificate⟩

/-- The honest diamond-with-triangle source still has a nonempty raw interior-edge endpoint
carrier: the shared diamond edge `dt12` contributes endpoint `1`. This keeps the later
endpoint-support obstruction focused on separation, not on vacuous emptiness of the raw carrier.
-/
theorem vertex_one_mem_interiorEdgeEndpointSupport_diamondWithTriangle :
    (1 : Fin 7) ∈ interiorEdgeEndpointSupport diamondWithTriangleEmbedding :=
  (mem_interiorEdgeEndpointSupport_iff diamondWithTriangleEmbedding).2
    ⟨dt12, dt12_mem_interiorEdgeSupport, vertex_one_mem_dt12⟩

theorem interiorEdgeEndpointSupport_nonempty_diamondWithTriangle :
    (interiorEdgeEndpointSupport diamondWithTriangleEmbedding).Nonempty :=
  ⟨1, vertex_one_mem_interiorEdgeEndpointSupport_diamondWithTriangle⟩

theorem diamondWithTriangle_interiorEdgeSupport_eq_singleton :
    interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
      diamondWithTriangleEmbedding.faces = {dt12} := by
  ext e
  constructor
  · intro he
    rcases diamondWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hcount :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt01 = 2 :=
        (mem_interiorEdgeSupport_iff
          diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces).1 he |>.2
      have hcount' :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt01 = 1 := by
        simpa [diamondWithTriangleEmbedding] using totalIncidenceCount_dt01
      rw [hcount'] at hcount
      omega
    · simp
    · have hcount :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt02 = 2 :=
        (mem_interiorEdgeSupport_iff
          diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces).1 he |>.2
      have hcount' :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt02 = 1 := by
        simpa [diamondWithTriangleEmbedding] using totalIncidenceCount_dt02
      rw [hcount'] at hcount
      omega
    · have hcount :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt13 = 2 :=
        (mem_interiorEdgeSupport_iff
          diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces).1 he |>.2
      have hcount' :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt13 = 1 := by
        simpa [diamondWithTriangleEmbedding] using totalIncidenceCount_dt13
      rw [hcount'] at hcount
      omega
    · have hcount :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt23 = 2 :=
        (mem_interiorEdgeSupport_iff
          diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces).1 he |>.2
      have hcount' :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt23 = 1 := by
        simpa [diamondWithTriangleEmbedding] using totalIncidenceCount_dt23
      rw [hcount'] at hcount
      omega
    · have hcount :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt45 = 2 :=
        (mem_interiorEdgeSupport_iff
          diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces).1 he |>.2
      have hcount' :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt45 = 1 := by
        simpa [diamondWithTriangleEmbedding] using totalIncidenceCount_dt45
      rw [hcount'] at hcount
      omega
    · have hcount :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt56 = 2 :=
        (mem_interiorEdgeSupport_iff
          diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces).1 he |>.2
      have hcount' :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt56 = 1 := by
        simpa [diamondWithTriangleEmbedding] using totalIncidenceCount_dt56
      rw [hcount'] at hcount
      omega
    · have hcount :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt64 = 2 :=
        (mem_interiorEdgeSupport_iff
          diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces).1 he |>.2
      have hcount' :
          totalIncidenceCount diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces dt64 = 1 := by
        simpa [diamondWithTriangleEmbedding] using totalIncidenceCount_dt64
      rw [hcount'] at hcount
      omega
  · intro he
    have he12 : e = dt12 := by simpa using he
    subst e
    exact dt12_mem_interiorEdgeSupport

theorem diamondWithTriangle_atMostOneInteriorEdgePerFace :
    ∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
      ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces)).card ≤ 1 := by
  intro f
  have hsing :
      interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
        diamondWithTriangleEmbedding.faces = {dt12} :=
    diamondWithTriangle_interiorEdgeSupport_eq_singleton
  have hsub :
      (diamondWithTriangleEmbedding.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces) ⊆ ({dt12} : Finset _) := by
    intro e he
    exact by
      simpa [hsing] using (Finset.mem_filter.1 he).2
  calc
    ((diamondWithTriangleEmbedding.faceBoundary f.1).filter
        (· ∈ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces)).card
        ≤ ({dt12} : Finset _).card := Finset.card_le_card hsub
    _ = 1 := by simp

theorem diamondWithTriangle_nonInteriorOnAmbient :
    ∀ (f : AmbientFace diamondWithTriangleEmbedding.faces) {e : diamondWithTriangleGraph.edgeSet},
      e ∈ diamondWithTriangleEmbedding.faceBoundary f.1 →
        e ∉ interiorEdgeSupport diamondWithTriangleEmbedding.faceBoundary
          diamondWithTriangleEmbedding.faces →
        e ∈
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
            diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  intro f e he hnonInterior
  have heSelected :
      e ∈ selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces := by
    rcases diamondWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact dt01_mem_selectedBoundarySupport
    · exact False.elim (hnonInterior dt12_mem_interiorEdgeSupport)
    · exact dt02_mem_selectedBoundarySupport
    · exact dt13_mem_selectedBoundarySupport
    · exact dt23_mem_selectedBoundarySupport
    · exact dt45_mem_selectedBoundarySupport
    · exact dt56_mem_selectedBoundarySupport
    · exact dt64_mem_selectedBoundarySupport
  exact
    diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData
      |>.hambientBoundaryCover heSelected

/-- Fallback edge function for diamond-with-triangle: picks a boundary edge for each face. -/
def diamondWithTriangleFallbackEdge :
    AmbientFace diamondWithTriangleEmbedding.faces → diamondWithTriangleGraph.edgeSet :=
  diamondWithTriangleOneCollarWitnessEdge

theorem diamondWithTriangleFallbackEdge_mem :
    ∀ f : AmbientFace diamondWithTriangleEmbedding.faces,
      diamondWithTriangleFallbackEdge f ∈ diamondWithTriangleEmbedding.faceBoundary f.1 := by
  classical
  intro f
  rcases
      diamondWithTriangleOneCollarGeometry.toPlanarBoundaryAnnulusDecomposition.exists_mem_collarFaces
        f with
    ⟨i, hfi⟩
  exact diamondWithTriangleOneCollarGeometry.hwitness i f hfi

/-- The diamond benchmark also satisfies the cardinal at-most-one sufficient-condition package
directly.  This gives a non-vacuous Tait-colored endpoint instance of the local criterion below,
not just a hand-built canonical witness choice. -/
theorem exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces →
            diamondWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : diamondWithTriangleGraph.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  exact
    ⟨diamondWithTriangleEmbedding, diamondWithTriangleClosedWalkAnnulusBoundarySource,
      diamondWithTriangleFallbackEdge, diamondWithTriangleFallbackEdge_mem,
      diamondWithTriangle_atMostOneInteriorEdgePerFace, diamondWithTriangle_nonInteriorOnAmbient⟩

/-- The route-level at-most-one constructor reconstructs canonical witness choice on the
Tait-colored diamond benchmark. -/
theorem
    diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace :
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
      diamondWithTriangleClosedWalkAnnulusBoundarySource
      diamondWithTriangleFallbackEdge
      diamondWithTriangleFallbackEdge_mem
      diamondWithTriangle_atMostOneInteriorEdgePerFace
      diamondWithTriangle_nonInteriorOnAmbient

/-- The explicit Tait-colored diamond benchmark reaches theorem-4.9 synthesis through the
generic at-most-one local criterion itself. -/
theorem
    diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
      diamondWithTriangleTaitEdgeColoring := by
  rcases
    diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace
      with ⟨choice⟩
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
      (G := diamondWithTriangleGraph)
      choice.toPlanarBoundaryAnnulusWitnessAssignment
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait

/-- Graph-level explicit-Tait endpoint for the diamond benchmark obtained through the route-level
at-most-one sufficient condition. -/
theorem
    exists_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      Theorem49BoundaryRootSynthesis emb diamondWithTriangleTaitEdgeColoring := by
  exact
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
      exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_diamondWithTriangleGraph
      diamondWithTriangleTaitEdgeColoring
      diamondWithTriangleTaitEdgeColoring_isTait

/-- End-to-end source-to-Theorem-4.9 calibration for the honest diamond benchmark.  The
closed-walk annulus source and explicit Tait coloring feed the at-most-one source route to
`Theorem49BoundaryRootSynthesis`, and the resulting theorem-4.9 synthesis fields give the raw
Definition 4.8 representative plus selected-boundary-kernel error decomposition for every
Kirchhoff chain on the same embedding. -/
theorem
    diamondWithTriangle_closedWalkSource_explicitTait_atMostOne_to_theorem49RawQuotientErrorPackage
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      ∀ x : diamondWithTriangleGraph.edgeSet → Color,
        x ∈
            kirchhoffSubmodule diamondWithTriangleGraph
              (selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding) →
          Theorem49BoundaryRawQuotientErrorPackage diamondWithTriangleEmbedding
            diamondWithTriangleTaitEdgeColoring x := by
  refine
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      diamondWithTriangleTaitEdgeColoring_isTait, ?_⟩
  intro x hx
  let hSynthesis :
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring :=
    diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace
  exact
    ⟨hSynthesis.rawKirchhoffRepresentative hx,
      hSynthesis.rawBoundaryKernelDecomposition hx⟩

theorem vertex_one_not_mem_selectedBoundaryInteriorEdgeEndpointVertices_diamondWithTriangle :
    (1 : Fin 7) ∉
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding :=
  not_mem_verticesAvoidingEdgeSupport_of_incident_boundary_edge
    dt01_mem_selectedBoundarySupport vertex_one_mem_dt01

theorem vertex_two_not_mem_selectedBoundaryInteriorEdgeEndpointVertices_diamondWithTriangle :
    (2 : Fin 7) ∉
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding :=
  not_mem_verticesAvoidingEdgeSupport_of_incident_boundary_edge
    dt02_mem_selectedBoundarySupport (by simp [dt02])

theorem selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle :
    selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ := by
  ext v
  constructor
  · intro hv
    rcases (mem_selectedBoundaryInteriorEdgeEndpointVertices_iff
        diamondWithTriangleEmbedding).1 hv with ⟨hvInterior, hAvoids⟩
    rcases hvInterior with ⟨e, heInterior, hve⟩
    have he12 : e = dt12 := by
      have heSingleton : e ∈ ({dt12} : Finset diamondWithTriangleGraph.edgeSet) := by
        simpa [diamondWithTriangle_interiorEdgeSupport_eq_singleton] using heInterior
      simpa using heSingleton
    subst e
    fin_cases v
    · simp [dt12] at hve
    · exact (hAvoids dt01 dt01_mem_selectedBoundarySupport vertex_one_mem_dt01).elim
    · exact (hAvoids dt02 dt02_mem_selectedBoundarySupport (by simp [dt02])).elim
    · simp [dt12] at hve
    · simp [dt12] at hve
    · simp [dt12] at hve
    · simp [dt12] at hve
  · intro hv
    simp at hv

theorem not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle :
    ¬ (selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding).Nonempty := by
  intro hv
  simp [selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle] at hv

/-- Local forcing-edge witness reused to compare the honest diamond benchmark against the current
parent-peel route. -/
def diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry :
    Theorem49ForcingInteriorEdgeObstruction.ForcingInteriorEdgeWitness diamondWithTriangleEmbedding
    where
  edge := dt12
  heInterior := dt12_mem_interiorEdgeSupport
  hforcing := by
    intro f hf
    exact exists_selectedBoundarySupport_of_dt12_mem_faceBoundary_diamondWithTriangle hf

/-- The diamond-with-triangle model is the positive benchmark for the current same-embedding
geometry ladder under an actual Tait coloring: the honest closed-walk source, canonical witness
choice, collar geometry, certificate-level witnesses, and theorem-4.9 boundary-root synthesis all
coexist on the same embedding. -/
theorem
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice,
      diamondWithTriangleTaitEdgeColoring_isTait,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasCollarLayerFacePeelWitnessData,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring⟩

/-- Parallel sealing of the diamond benchmark: on the same genuine cyclic source embedding, the
full current same-embedding positive geometry stack and theorem-4.9 synthesis endpoint coexist
with complete failure of the newer projected nonempty endpoint, because selected-boundary
purification deletes both endpoints of the unique interior edge. -/
theorem
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_nonemptyProjectedSynthesis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice,
      diamondWithTriangleTaitEdgeColoring_isTait,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasCollarLayerFacePeelWitnessData,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      by
        intro hProjected
        exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle
          hProjected.nonemptySynthesis.carrier_nonempty⟩

/-- Graph-level packaging of the same diamond obstruction: the graph admits an honest
closed-walk source together with the full current same-embedding geometry stack and theorem-4.9
synthesis for an explicit Tait coloring, yet the projected nonempty endpoint still fails on that
same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) ∧
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_nonemptyProjectedSynthesis
      with ⟨hSource, hChoice, hTait, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth, _,
        hNoProjected⟩
  rcases hSource with ⟨_source⟩
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      hChoice,
      diamondWithTriangleTaitEdgeColoring,
      hTait,
      hCollar,
      hPrev,
      hLayer,
      hHeight,
      hCert,
      hWell,
      hSynth,
      hNoProjected⟩

/-- The diamond benchmark refutes the live converse from the full current same-embedding
geometry stack back to the projected nonempty theorem-4.9 endpoint.  Even an honest closed-walk
annulus source with canonical witness choice, explicit Tait coloring, annulus collar geometry,
repaired previous-boundary witness geometry, all currently sufficient peel witnesses, and the
full theorem-4.9 synthesis package does not force `Theorem49BoundaryRootNonemptyProjectedSynthesis`
on the same embedding. -/
theorem
    not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              source.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
                Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
                Nonempty
                  (BoundaryRootedFacePeelCertificate emb.faces.attach
                    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
                Theorem49BoundaryRootSynthesis emb C →
                Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
              Theorem49BoundaryRootSynthesis emb C →
              Theorem49BoundaryRootNonemptyProjectedSynthesis emb C) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph
      with ⟨emb, source, hChoice, C, hC, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoProjected⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoProjected (hTarget hChoice C hC hCollar hPrev hLayer hHeight hCert hWell hSynth)⟩

/-- Parallel sealing of the diamond benchmark against the current interior-dual route: on the
same genuine cyclic source embedding, the full current same-embedding positive geometry stack and
the explicit-Tait theorem-4.9 synthesis endpoint already hold, yet generic
`InteriorDualBoundaryRootAdjDistancePeelData` still fails. -/
theorem
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_interiorDualBoundaryRootAdjDistancePeelData
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice,
      diamondWithTriangleTaitEdgeColoring_isTait,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasCollarLayerFacePeelWitnessData,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- Graph-level packaging of the same diamond obstruction against the earlier generic
interior-dual route: the graph admits an honest closed-walk source together with the full
current same-embedding geometry stack and theorem-4.9 synthesis for an explicit Tait coloring,
yet generic `InteriorDualBoundaryRootAdjDistancePeelData` still fails on that same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) ∧
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Nonempty
                (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_interiorDualBoundaryRootAdjDistancePeelData
      with ⟨hSource, hChoice, hTait, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoIDBRAD⟩
  rcases hSource with ⟨_source⟩
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      hChoice,
      diamondWithTriangleTaitEdgeColoring,
      hTait,
      hCollar,
      hPrev,
      hLayer,
      hHeight,
      hCert,
      hWell,
      hSynth,
      hNoIDBRAD⟩

/-- The diamond benchmark also refutes the converse from the full current same-embedding
geometry stack and theorem-4.9 synthesis back to the earlier generic
`InteriorDualBoundaryRootAdjDistancePeelData` package. -/
theorem
    not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              source.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
                Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
                Nonempty
                  (BoundaryRootedFacePeelCertificate emb.faces.attach
                    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty
                  (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
              Theorem49BoundaryRootSynthesis emb C →
              Nonempty
                (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangleGraph
      with ⟨emb, source, hChoice, C, hC, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoIDBRAD⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoIDBRAD (hTarget hChoice C hC hCollar hPrev hLayer hHeight hCert hWell hSynth)⟩

/-- The same genuine cyclic diamond benchmark also defeats the source-preserving annulus-root
adjacency-distance target itself: even the full current same-embedding positive geometry stack
and the explicit-Tait theorem-4.9 synthesis endpoint do not force
`PlanarBoundaryAnnulusRootAdjDistancePeelData` on that embedding. -/
theorem
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_planarBoundaryAnnulusRootAdjDistancePeelData
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData diamondWithTriangleEmbedding) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice,
      diamondWithTriangleTaitEdgeColoring_isTait,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasCollarLayerFacePeelWitnessData,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- Parallel sealing of the diamond benchmark against the live parent-peel target: on the same
genuine cyclic source embedding, the full current same-embedding positive geometry stack and the
explicit-Tait theorem-4.9 synthesis endpoint already hold, yet the stronger
`PlanarBoundaryAnnulusRootParentPeelData` package still fails. -/
theorem
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_planarBoundaryAnnulusRootParentPeelData
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      diamondWithTriangleClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice,
      diamondWithTriangleTaitEdgeColoring_isTait,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasCollarLayerFacePeelWitnessData,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- Graph-level packaging of the same diamond obstruction: the graph admits an honest
closed-walk source together with the full current same-embedding geometry stack and theorem-4.9
synthesis for an explicit Tait coloring, yet the source-preserving annulus-root adj-distance
package still fails on that same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) ∧
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_planarBoundaryAnnulusRootAdjDistancePeelData
      with ⟨hSource, hChoice, hTait, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoAdj⟩
  rcases hSource with ⟨_source⟩
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      hChoice,
      diamondWithTriangleTaitEdgeColoring,
      hTait,
      hCollar,
      hPrev,
      hLayer,
      hHeight,
      hCert,
      hWell,
      hSynth,
      hNoAdj⟩

/-- The diamond benchmark refutes the converse from the full current same-embedding geometry
stack and theorem-4.9 synthesis back to the source-preserving annulus-root adjacency-distance
package.  Even an honest closed-walk annulus source with canonical witness choice, explicit
Tait coloring, annulus collar geometry, repaired previous-boundary witness geometry, all
currently sufficient peel witnesses, and the full theorem-4.9 synthesis package does not force
`PlanarBoundaryAnnulusRootAdjDistancePeelData` on the same embedding. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              source.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
                Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
                Nonempty
                  (BoundaryRootedFacePeelCertificate emb.faces.attach
                    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
              Theorem49BoundaryRootSynthesis emb C →
              Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph
      with ⟨emb, source, hChoice, C, hC, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoAdj⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoAdj (hTarget hChoice C hC hCollar hPrev hLayer hHeight hCert hWell hSynth)⟩

/-- Graph-level packaging of the same diamond obstruction against the live parent-peel target:
the graph admits an honest closed-walk source together with the full current same-embedding
geometry stack and theorem-4.9 synthesis for an explicit Tait coloring, yet the stronger
annulus-root parent-peel package still fails on that same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) ∧
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) ∧
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) ∧
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_planarBoundaryAnnulusRootParentPeelData
      with ⟨hSource, hChoice, hTait, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoParent⟩
  rcases hSource with ⟨_source⟩
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      hChoice,
      diamondWithTriangleTaitEdgeColoring,
      hTait,
      hCollar,
      hPrev,
      hLayer,
      hHeight,
      hCert,
      hWell,
      hSynth,
      hNoParent⟩

/-- The diamond benchmark also refutes the converse from the full current same-embedding
geometry stack and theorem-4.9 synthesis back to the live annulus-root parent-peel target. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty
            (PlanarBoundaryCanonicalWitnessChoice
              source.toPlanarBoundaryAnnulusBoundaryData) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
                Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
                Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
                Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
                Nonempty
                  (BoundaryRootedFacePeelCertificate emb.faces.attach
                    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
                Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb source =>
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
              Nonempty (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb) →
              Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) →
              Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData emb) →
              Nonempty
                (BoundaryRootedFacePeelCertificate emb.faces.attach
                  (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
              Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData emb) →
              Theorem49BoundaryRootSynthesis emb C →
              Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_canonicalWitnessChoice_and_taitEdgeColoring_and_currentSufficientSameEmbeddingGeometry_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph
      with ⟨emb, source, hChoice, C, hC, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynth,
        hNoParent⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact
        hNoParent (hTarget hChoice C hC hCollar hPrev hLayer hHeight hCert hWell hSynth)⟩

/-- Consolidated route diagnosis for the genuine cyclic diamond benchmark: the same explicit
Tait-colored embedding already carries the full current same-embedding positive geometry stack and
the theorem-4.9 synthesis endpoint, while its raw interior-edge endpoint carrier is still
nonempty, its selected-boundary-purified carrier is empty, the projected nonempty endpoint fails,
generic interior-dual boundary-root adjacency-distance data fails, and the live parent-peel
package fails as well. -/
theorem diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_consolidatedRouteDiagnosis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          diamondWithTriangleClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
          diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      (interiorEdgeEndpointSupport diamondWithTriangleEmbedding).Nonempty ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_nonemptyProjectedSynthesis
      with ⟨hSource, hChoice, hTait, hCollar, hPrev, hLayer, hHeight, hCert, hWell, hSynthesis,
        hPurifiedEmpty, hNotProjected⟩
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_interiorDualBoundaryRootAdjDistancePeelData
      with ⟨_, _, _, _, _, _, _, _, _, _, hNoIDBRAD⟩
  rcases
    diamondWithTriangle_explicitTait_currentSufficientSameEmbeddingGeometry_without_planarBoundaryAnnulusRootParentPeelData
      with ⟨_, _, _, _, _, _, _, _, _, _, hNoParentPeel⟩
  exact
    ⟨hSource,
      hChoice,
      hTait,
      hCollar,
      hPrev,
      hLayer,
      hHeight,
      hCert,
      hWell,
      hSynthesis,
      interiorEdgeEndpointSupport_nonempty_diamondWithTriangle,
      hPurifiedEmpty,
      hNotProjected,
      hNoIDBRAD,
      hNoParentPeel⟩

/-- The same explicit Tait-colored positive benchmark already reaches the full theorem-4.9
synthesis endpoint while still failing the generic interior-dual boundary-root adj-distance
package.  So the current generic adj-distance burden is not necessary even on a genuine cyclic
synthesis model. -/
theorem diamondWithTriangle_explicitTait_synthesis_without_interiorDualBoundaryRootAdjDistancePeelData
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- The same explicit Tait-colored positive benchmark already reaches the full theorem-4.9
synthesis endpoint while still failing the source-preserving annulus-root adj-distance target. -/
theorem diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData diamondWithTriangleEmbedding) := by
  exact
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- The same explicit Tait-colored positive benchmark already reaches the full theorem-4.9
synthesis endpoint while still failing the live parent-oriented annulus-root target.  So the
current parent-peel burden is not necessary even on a genuine cyclic synthesis model. -/
theorem diamondWithTriangle_explicitTait_synthesis_without_planarBoundaryAnnulusRootParentPeelData
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
  exact
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- The same explicit Tait-colored positive benchmark does not reach the nonempty-carrier
version of the theorem-4.9 synthesis target: the selected-boundary purification deletes both
endpoints of its sole interior edge. -/
theorem not_theorem49BoundaryRootNonemptySynthesis_diamondWithTriangle_explicitTait
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ Theorem49BoundaryRootNonemptySynthesis diamondWithTriangleEmbedding
      diamondWithTriangleTaitEdgeColoring := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle
    h.carrier_nonempty

/-- No coloring can put the diamond-with-triangle embedding into the current projected nonempty
theorem-4.9 endpoint: that package contains the nonempty-carrier synthesis package, while the
selected-boundary purification has already deleted both endpoints of the only interior edge. -/
theorem not_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangle
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)]
    (C0 : diamondWithTriangleGraph.EdgeColoring Color) :
    ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding C0 := by
  intro h
  exact not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle
    h.nonemptySynthesis.carrier_nonempty

/-- Compact status theorem for the explicit Tait-colored diamond benchmark: current synthesis is
available on the same embedding, but the nonempty selected-boundary interior-edge endpoint target
is not. -/
theorem diamondWithTriangle_explicitTait_synthesis_has_empty_selectedBoundaryInteriorCarrier
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ Theorem49BoundaryRootNonemptySynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring := by
  exact
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_theorem49BoundaryRootNonemptySynthesis_diamondWithTriangle_explicitTait⟩

/-- The explicit Tait-colored diamond benchmark reaches the current synthesis target through the
same-embedding geometry stack, but the newer projected nonempty endpoint is blocked outright by
the empty purified endpoint carrier. -/
theorem diamondWithTriangle_explicitTait_synthesis_blocks_nonemptyProjectedSynthesis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring := by
  exact
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangle
        diamondWithTriangleTaitEdgeColoring⟩

/-- The at-most-one route reaches the same explicit-Tait diamond endpoint, but it still does not
solve the nonempty-carrier obligation: selected-boundary purification deletes both endpoints of
the sole interior edge. -/
theorem diamondWithTriangle_explicitTait_atMostOne_synthesis_has_empty_selectedBoundaryInteriorCarrier
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ Theorem49BoundaryRootNonemptySynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring := by
  exact
    ⟨diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring_via_atMostOneInteriorEdgePerFace,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_theorem49BoundaryRootNonemptySynthesis_diamondWithTriangle_explicitTait⟩

/-- Honest annulus source data on the diamond-with-triangle embedding is compatible with the
weak one-collar annulus geometry and its attached certificate, but still incompatible with the
construction-side parent-witness orientation shell.  This shows the certificate lane sits strictly
earlier than the parent-orientation lane even on a genuine cyclic source model. -/
theorem
    closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_without_parentWitnessOrientation_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      ¬ diamondWithTriangleOneCollarConstruction.ParentWitnessOrientation := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      not_diamondWithTriangleOneCollarConstructionParentWitnessOrientation⟩

/-- The same honest-source one-collar annulus geometry already reaches the attached-certificate
endpoint on the diamond-with-triangle embedding, while the interior-dual boundary-root
adjacency-distance package remains empty there.  This is a genuine source-side witness that the
certificate branch is available strictly earlier than the current interior-dual route. -/
theorem
    closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_without_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
        diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faceBoundary) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- The same honest-source one-collar annulus geometry and attached certificate still do not
force the live parent-oriented annulus-root target on the diamond-with-triangle embedding.  So
the certificate lane is already strictly earlier than the current parent-peel burden on a genuine
cyclic source model. -/
theorem
    closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData diamondWithTriangleEmbedding) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- Graph-level packaging of the honest diamond collar/certificate obstruction against the
generic interior-dual route: the graph admits an honest closed-walk annulus source together with
weak one-collar geometry, an attached rooted face-peel certificate, and an explicit Tait coloring
reaching theorem-4.9 synthesis, yet generic boundary-root adjacency-distance data still fails on
that same embedding. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Nonempty
                (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleTaitEdgeColoring,
      diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangle⟩

/-- The honest diamond collar/certificate benchmark refutes the converse from weak one-collar
geometry, an attached rooted face-peel certificate, and explicit theorem-4.9 synthesis back to
the generic boundary-root adjacency-distance package. -/
theorem
    not_forall_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty
                  (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Theorem49BoundaryRootSynthesis emb C →
              Nonempty
                (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_interiorDualBoundaryRootAdjDistancePeelData_diamondWithTriangleGraph
      with ⟨emb, source, hCollar, hCert, C, hC, hSynth, hNoIDBRAD⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoIDBRAD (hTarget hCollar hCert C hC hSynth)⟩

/-- Graph-level packaging of the same honest diamond collar/certificate obstruction against the
source-preserving annulus-root adjacency-distance route target. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleTaitEdgeColoring,
      diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- The honest diamond collar/certificate benchmark also refutes the converse from that same
certificate-plus-synthesis shell back to the source-preserving annulus-root adj-distance target. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Theorem49BoundaryRootSynthesis emb C →
              Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootAdjDistancePeelData_diamondWithTriangleGraph
      with ⟨emb, source, hCollar, hCert, C, hC, hSynth, hNoAdj⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoAdj (hTarget hCollar hCert C hC hSynth)⟩

/-- Graph-level packaging of the same honest diamond collar/certificate obstruction against the
live source-fixed annulus-root parent-peel target. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleTaitEdgeColoring,
      diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      Theorem49ForcingInteriorEdgeObstruction.not_nonempty_planarBoundaryAnnulusRootParentPeelData
        diamondWithTriangleForcingInteriorEdgeWitness_honestGeometry⟩

/-- The honest diamond collar/certificate benchmark refutes the converse from weak annulus
geometry, attached certificate, and explicit theorem-4.9 synthesis back to the live parent-peel
route target. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Theorem49BoundaryRootSynthesis emb C →
                Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Theorem49BoundaryRootSynthesis emb C →
              Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb)) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_planarBoundaryAnnulusRootParentPeelData_diamondWithTriangleGraph
      with ⟨emb, source, hCollar, hCert, C, hC, hSynth, hNoParent⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoParent (hTarget hCollar hCert C hC hSynth)⟩

/-- The weak honest collar/certificate shell already reaches explicit theorem-4.9 synthesis on
the diamond benchmark, but the selected-boundary-purified carrier is still empty, so the
projected nonempty endpoint fails there as well. -/
theorem
    diamondWithTriangle_explicitTait_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_theorem49BoundaryRootSynthesis_blocks_nonemptyProjectedSynthesis
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      IsTaitEdgeColoring diamondWithTriangleGraph diamondWithTriangleTaitEdgeColoring ∧
      Theorem49BoundaryRootSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis diamondWithTriangleEmbedding
        diamondWithTriangleTaitEdgeColoring := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangle
        diamondWithTriangleTaitEdgeColoring⟩

/-- Graph-level packaging of the same honest diamond collar/certificate obstruction against the
projected nonempty theorem-4.9 endpoint itself. -/
theorem
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) ∧
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) ∧
          ∃ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C ∧
              Theorem49BoundaryRootSynthesis emb C ∧
              ¬ Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  exact
    ⟨diamondWithTriangleEmbedding,
      diamondWithTriangleClosedWalkAnnulusBoundarySource,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      diamondWithTriangleTaitEdgeColoring,
      diamondWithTriangleTaitEdgeColoring_isTait,
      diamondWithTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring,
      not_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangle
        diamondWithTriangleTaitEdgeColoring⟩

/-- The honest diamond collar/certificate benchmark also refutes the converse from that weak
certificate-plus-synthesis shell to the projected nonempty theorem-4.9 endpoint. -/
theorem
    not_forall_theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_diamondWithTriangleGraph
    [Fintype diamondWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (diamondWithTriangleGraph.edgeSet → Color)] :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary diamondWithTriangleGraph,
        ∀ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
            Nonempty
              (BoundaryRootedFacePeelCertificate emb.faces.attach
                (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
            ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
              IsTaitEdgeColoring diamondWithTriangleGraph C →
                Theorem49BoundaryRootSynthesis emb C →
                Theorem49BoundaryRootNonemptyProjectedSynthesis emb C := by
  refine
    not_forall_target_of_exists_embedding_closedWalkAnnulusBoundarySource_without_target
      (Target := fun emb _source =>
        Nonempty (PlanarBoundaryAnnulusCollarGeometry emb) →
          Nonempty
            (BoundaryRootedFacePeelCertificate emb.faces.attach
              (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)) →
          ∀ C : diamondWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring diamondWithTriangleGraph C →
              Theorem49BoundaryRootSynthesis emb C →
              Theorem49BoundaryRootNonemptyProjectedSynthesis emb C) ?_
  rcases
    exists_embedding_closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_and_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_without_theorem49BoundaryRootNonemptyProjectedSynthesis_diamondWithTriangleGraph
      with ⟨emb, source, hCollar, hCert, C, hC, hSynth, hNoProjected⟩
  exact
    ⟨emb, source, by
      intro hTarget
      exact hNoProjected (hTarget hCollar hCert C hC hSynth)⟩

/-- Genuine honest-source annulus geometry and the attached certificate endpoint still do not
force the endpoint-support separation needed by the current non-vacuous annulus-root repair.
The diamond-with-triangle embedding already has an honest closed-walk source, a one-collar
annulus geometry, an attached rooted face-peel certificate, and a nonempty raw interior-edge
endpoint carrier, yet the shared diamond endpoint still lies on the selected boundary support. -/
theorem
    closedWalkAnnulusBoundarySource_and_annulusCollarGeometry_and_attachedRootedFacePeelCertificate_with_nonempty_interiorEdgeEndpointSupport_without_endpointSupport_disjoint_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryAnnulusCollarGeometry diamondWithTriangleEmbedding) ∧
      Nonempty
        (BoundaryRootedFacePeelCertificate diamondWithTriangleEmbedding.faces.attach
          (ambientFaceBoundary (allFaces := diamondWithTriangleEmbedding.faces)
            diamondWithTriangleEmbedding.faceBoundary)) ∧
      (interiorEdgeEndpointSupport diamondWithTriangleEmbedding).Nonempty ∧
      ¬ Disjoint (interiorEdgeEndpointSupport diamondWithTriangleEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces)) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarGeometry⟩,
      diamondWithTriangleOneCollarGeometry_hasAttachedRootedFacePeelCertificate,
      interiorEdgeEndpointSupport_nonempty_diamondWithTriangle,
      not_endpointSupport_disjoint_diamondWithTriangle⟩

/-- The same honest source model already satisfies the repaired previous-boundary witness
geometry and therefore reaches the boundary-aware well-founded peel endpoint, but the raw
interior-edge endpoint carrier still meets the selected boundary support. So endpoint-support
disjointness is not forced even by the corrected annulus geometry surface that feeds the
well-founded certificate route. -/
theorem
    closedWalkAnnulusBoundarySource_and_previousBoundaryWitnessGeometry_and_wellFoundedFacePeelWitnessData_with_nonempty_interiorEdgeEndpointSupport_without_endpointSupport_disjoint_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      (interiorEdgeEndpointSupport diamondWithTriangleEmbedding).Nonempty ∧
      ¬ Disjoint (interiorEdgeEndpointSupport diamondWithTriangleEmbedding)
        (edgeEndpointSupport
          (selectedBoundarySupport diamondWithTriangleEmbedding.faceBoundary
            diamondWithTriangleEmbedding.faces diamondWithTriangleEmbedding.faces)) := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      interiorEdgeEndpointSupport_nonempty_diamondWithTriangle,
      not_endpointSupport_disjoint_diamondWithTriangle⟩

/-- The stronger honest-source countermodel reaches the repaired previous-boundary witness
geometry and the derived boundary-aware well-founded peel endpoint, and still has a nonempty raw
interior-edge endpoint carrier while the purified selected-boundary carrier is empty.  This
directly blocks non-vacuous endpoint purification on the current honest annulus route. -/
theorem
    closedWalkAnnulusBoundarySource_and_previousBoundaryWitnessGeometry_and_wellFoundedFacePeelWitnessData_with_nonempty_interiorEdgeEndpointSupport_and_empty_selectedBoundaryInteriorEdgeEndpointVertices_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryWellFoundedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      (interiorEdgeEndpointSupport diamondWithTriangleEmbedding).Nonempty ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ (selectedBoundaryInteriorEdgeEndpointVertices
        diamondWithTriangleEmbedding).Nonempty := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasWellFoundedFacePeelWitnessData,
      interiorEdgeEndpointSupport_nonempty_diamondWithTriangle,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle⟩

/-- The same honest-source countermodel already reaches the explicit height-ordered peel witness
surface obtained from the corrected previous-boundary annulus geometry, and still has nonempty raw
interior-edge endpoint support while the purified selected-boundary carrier is empty. So even this
stronger layered peel interface does not force the non-vacuous endpoint carrier needed by the
current theorem-4.9 repair line. -/
theorem
    closedWalkAnnulusBoundarySource_and_previousBoundaryWitnessGeometry_and_heightOrderedFacePeelWitnessData_with_nonempty_interiorEdgeEndpointSupport_and_empty_selectedBoundaryInteriorEdgeEndpointVertices_diamondWithTriangle :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource diamondWithTriangleEmbedding) ∧
      Nonempty
        (PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry diamondWithTriangleEmbedding) ∧
      Nonempty (PlanarBoundaryHeightOrderedFacePeelWitnessData diamondWithTriangleEmbedding) ∧
      (interiorEdgeEndpointSupport diamondWithTriangleEmbedding).Nonempty ∧
      selectedBoundaryInteriorEdgeEndpointVertices diamondWithTriangleEmbedding = ∅ ∧
      ¬ (selectedBoundaryInteriorEdgeEndpointVertices
        diamondWithTriangleEmbedding).Nonempty := by
  exact
    ⟨nonempty_closedWalkAnnulusBoundarySource_diamondWithTriangle,
      ⟨diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry⟩,
      diamondWithTriangleOneCollarPreviousBoundaryWitnessGeometry_hasHeightOrderedFacePeelWitnessData,
      interiorEdgeEndpointSupport_nonempty_diamondWithTriangle,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_diamondWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_diamondWithTriangle⟩

/-- A general sufficient condition for canonical witness choice on an honest source.

If every face has at most one interior boundary edge, every face has a fallback boundary edge, and
every non-interior boundary edge already lies on the source's outer or inner ambient boundary,
then the canonical facewise witness choice exists.  The witness is the unique interior edge on a
face when one exists, and the fallback edge otherwise. -/
theorem exists_canonicalWitnessChoice_of_closedWalkSource_with_atMostOneInteriorEdgePerFace
    [DecidableEq V]
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hfallback : ∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1)
    (h_at_most_one_interior :
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
            (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
          (1 : ℕ))
    (h_nonInterior_on_ambient :
      ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
        e ∈ emb.faceBoundary f.1 →
          e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
          e ∈
            source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
              source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice source.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace
      source fallbackEdge hfallback h_at_most_one_interior h_nonInterior_on_ambient

/-- Graph-level version of the at-most-one-interior-edge sufficient condition. -/
theorem admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkSource_with_atMostOneInteriorEdgePerFace
    [DecidableEq V]
    {G : SimpleGraph V}
    (hex :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                  ((emb.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                    (1 : ℕ)) ∧
                  ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                    e ∈ emb.faceBoundary f.1 →
                      e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                      e ∈
                        source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                          source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment G := by
  classical
  obtain ⟨emb, source, fallbackEdge, hfb, hatmost, hnonInterior⟩ := hex
  exact
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_planarBoundaryCanonicalWitnessChoice
      ⟨emb, source.toPlanarBoundaryAnnulusBoundaryData,
        exists_canonicalWitnessChoice_of_closedWalkSource_with_atMostOneInteriorEdgePerFace source
          fallbackEdge hfb hatmost hnonInterior⟩

/-- Closed-walk annulus source together with at-most-one-interior-edge-per-face directly
implies weak collar geometry. This chains witness-assignment derivation from the at-most-one
interior condition with the existing witness-to-geometry bridge. -/
theorem admitsPlanarBoundaryAnnulusCollarGeometry_of_exists_closedWalkSource_with_atMostOneInteriorEdgePerFace
    [DecidableEq V]
    {G : SimpleGraph V}
    (hex :
      ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
            (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
              (∀ f : AmbientFace emb.faces,
                  ((emb.faceBoundary f.1).filter
                      (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                    (1 : ℕ)) ∧
                  ∀ (f : AmbientFace emb.faces) {e : G.edgeSet},
                    e ∈ emb.faceBoundary f.1 →
                      e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                      e ∈
                        source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                          source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    AdmitsPlanarBoundaryAnnulusCollarGeometry G :=
  admitsPlanarBoundaryAnnulusCollarGeometry_of_admitsPlanarBoundaryAnnulusWitnessAssignment
    (admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkSource_with_atMostOneInteriorEdgePerFace
      hex)

/-- The chained-diamonds canonical witness selector is a valid fallback boundary edge on every
ambient face.  This is the facewise fallback component needed to instantiate the generic
at-most-one-interior-edge criterion. -/
theorem chainedDiamondsCanonicalWitnessEdge_mem :
    ∀ f : AmbientFace chainedDiamondsWithTriangleEmbedding.faces,
      chainedDiamondsCanonicalWitnessEdge f ∈
        chainedDiamondsWithTriangleEmbedding.faceBoundary f.1 := by
  intro f
  obtain ⟨⟨i, hi⟩, hf⟩ := f
  interval_cases i <;>
    simp [chainedDiamondsCanonicalWitnessEdge, chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsWithTriangleFaceBoundary, cdt01, cdt12, cdt02, cdt13, cdt23,
      cdt34, cdt45, cdt35, cdt46, cdt56, cdt78, cdt89, cdt97]

/-- On the chained-diamonds honest source, every face-boundary edge that is not one of the two
interior edges already lies on the extracted outer or inner ambient annulus boundary. -/
theorem chainedDiamonds_nonInteriorOnAmbient :
    ∀ (f : AmbientFace chainedDiamondsWithTriangleEmbedding.faces)
        {e : chainedDiamondsWithTriangleGraph.edgeSet},
      e ∈ chainedDiamondsWithTriangleEmbedding.faceBoundary f.1 →
        e ∉ interiorEdgeSupport chainedDiamondsWithTriangleEmbedding.faceBoundary
          chainedDiamondsWithTriangleEmbedding.faces →
        e ∈
          chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
            chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  intro _f e _he hnonInterior
  have heSelected :
      e ∈ selectedBoundarySupport chainedDiamondsWithTriangleEmbedding.faceBoundary
        chainedDiamondsWithTriangleEmbedding.faces chainedDiamondsWithTriangleEmbedding.faces := by
    rcases chainedDiamondsWithTriangle_edge_eq e with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cdt01_mem_selectedBoundarySupport
    · exact False.elim (hnonInterior cdt12_mem_interiorEdgeSupport)
    · exact cdt02_mem_selectedBoundarySupport
    · exact cdt13_mem_selectedBoundarySupport
    · exact cdt23_mem_selectedBoundarySupport
    · exact cdt34_mem_selectedBoundarySupport
    · exact False.elim (hnonInterior cdt45_mem_interiorEdgeSupport)
    · exact cdt35_mem_selectedBoundarySupport
    · exact cdt46_mem_selectedBoundarySupport
    · exact cdt56_mem_selectedBoundarySupport
    · exact cdt78_mem_selectedBoundarySupport
    · exact cdt89_mem_selectedBoundarySupport
    · exact cdt97_mem_selectedBoundarySupport
  exact
    chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData
      |>.hambientBoundaryCover heSelected

/-- Concrete non-vacuity of the at-most-one-interior-edge sufficient condition: the
chained-diamonds honest closed-walk source supplies all local hypotheses of the generic
criterion. -/
theorem
    exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces →
            chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  exact
    ⟨chainedDiamondsWithTriangleEmbedding, chainedDiamondsClosedWalkAnnulusBoundarySource,
      chainedDiamondsCanonicalWitnessEdge, chainedDiamondsCanonicalWitnessEdge_mem,
      chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace,
      chainedDiamonds_nonInteriorOnAmbient⟩

/-- Status theorem for the chained-diamonds at-most-one benchmark: it inhabits the local
at-most-one source package, but it cannot supply either a surviving purified carrier or a Tait
coloring. -/
theorem chainedDiamonds_atMostOne_source_has_empty_carrier_and_no_tait :
    (∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fallbackEdge : AmbientFace emb.faces → chainedDiamondsWithTriangleGraph.edgeSet,
          (∀ f : AmbientFace emb.faces, fallbackEdge f ∈ emb.faceBoundary f.1) ∧
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
                (1 : ℕ)) ∧
              ∀ (f : AmbientFace emb.faces) {e : chainedDiamondsWithTriangleGraph.edgeSet},
                e ∈ emb.faceBoundary f.1 →
                  e ∉ interiorEdgeSupport emb.faceBoundary emb.faces →
                  e ∈
                    source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
                      source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
      selectedBoundaryInteriorEdgeEndpointVertices chainedDiamondsWithTriangleEmbedding = ∅ ∧
      ¬ (selectedBoundaryInteriorEdgeEndpointVertices
          chainedDiamondsWithTriangleEmbedding).Nonempty ∧
      ¬ ∃ C : chainedDiamondsWithTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C := by
  exact
    ⟨exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_chainedDiamondsWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_chainedDiamondsWithTriangle,
      not_exists_taitEdgeColoring_chainedDiamondsWithTriangleGraph⟩

/-- The generic at-most-one-interior-edge criterion reconstructs the chained-diamonds canonical
witness choice; this proves the criterion is inhabited by a model with two distinct interior
edges. -/
theorem
    chainedDiamondsClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace :
    Nonempty
      (PlanarBoundaryCanonicalWitnessChoice
        chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData) := by
  exact
    exists_canonicalWitnessChoice_of_closedWalkSource_with_atMostOneInteriorEdgePerFace
      chainedDiamondsClosedWalkAnnulusBoundarySource
      chainedDiamondsCanonicalWitnessEdge
      chainedDiamondsCanonicalWitnessEdge_mem
      chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace
      chainedDiamonds_nonInteriorOnAmbient

/-- Graph-level witness-assignment admissibility for chained diamonds obtained through the
generic at-most-one-interior-edge theorem, not through the hand-built canonical witness object. -/
theorem
    chainedDiamondsWithTriangleGraph_admitsPlanarBoundaryAnnulusWitnessAssignment_via_atMostOneInteriorEdgePerFace :
    AdmitsPlanarBoundaryAnnulusWitnessAssignment chainedDiamondsWithTriangleGraph := by
  exact
    admitsPlanarBoundaryAnnulusWitnessAssignment_of_exists_closedWalkSource_with_atMostOneInteriorEdgePerFace
      exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph

/-- Graph-level collar-geometry admissibility for chained diamonds obtained through the generic
at-most-one-interior-edge sufficient condition. -/
theorem
    chainedDiamondsWithTriangleGraph_admitsPlanarBoundaryAnnulusCollarGeometry_via_atMostOneInteriorEdgePerFace :
    AdmitsPlanarBoundaryAnnulusCollarGeometry chainedDiamondsWithTriangleGraph := by
  exact
    admitsPlanarBoundaryAnnulusCollarGeometry_of_exists_closedWalkSource_with_atMostOneInteriorEdgePerFace
      exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph

/-- Conditional theorem-4.9 synthesis for chained diamonds obtained through the generic
at-most-one-interior-edge sufficient condition, rather than through the hand-built one-collar
geometry.  The statement remains conditional on a Tait coloring, as this benchmark is primarily
a non-vacuity test for the local annulus geometry criterion. -/
theorem
    chainedDiamondsWithTriangleEmbedding_theorem49BoundaryRootSynthesis_via_atMostOneInteriorEdgePerFace
    [Fintype chainedDiamondsWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (chainedDiamondsWithTriangleGraph.edgeSet → Color)]
    (C₀ : chainedDiamondsWithTriangleGraph.EdgeColoring Color)
    (hC₀ : IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C₀) :
    Theorem49BoundaryRootSynthesis chainedDiamondsWithTriangleEmbedding C₀ := by
  rcases
    chainedDiamondsClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace
      with ⟨choice⟩
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
      (G := chainedDiamondsWithTriangleGraph)
      choice.toPlanarBoundaryAnnulusWitnessAssignment C₀ hC₀

/-- Graph-level theorem-4.9 synthesis for chained diamonds through the generic at-most-one
sufficient condition. -/
theorem
    exists_theorem49BoundaryRootSynthesis_chainedDiamondsWithTriangleGraph_via_atMostOneInteriorEdgePerFace
    [Fintype chainedDiamondsWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (chainedDiamondsWithTriangleGraph.edgeSet → Color)]
    (C₀ : chainedDiamondsWithTriangleGraph.EdgeColoring Color)
    (hC₀ : IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    exists_theorem49BoundaryRootSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_atMostOneInteriorEdgePerFace_direct
      exists_closedWalkSource_with_atMostOneInteriorEdgePerFace_chainedDiamondsWithTriangleGraph
      C₀ hC₀

/-- The chained-diamonds at-most-one benchmark already inhabits the exact one-collar current-
boundary shell and the split-annulus witness-assignment surface on the same honest closed-walk
source, but the purified carrier stays empty and no Tait coloring exists.  So on this branch the
remaining obstruction is not current-boundary or witness-assignment packaging. -/
theorem
    exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_chainedDiamondsWithTriangleGraph_with_empty_carrier_and_without_taitEdgeColoring :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) ∧
        Nonempty
          (PlanarBoundaryAnnulusWitnessAssignment
            (planarBoundaryAnnulusDecomposition_of_boundaryData
              source.toPlanarBoundaryAnnulusBoundaryData)) ∧
        selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ ∧
        ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
        ¬ ∃ C : chainedDiamondsWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData chainedDiamondsWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData := by
    exact
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        chainedDiamondsClosedWalkAnnulusBoundarySource
        chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace
  have hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData)) := by
    rcases
      chainedDiamondsClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace
        with ⟨choice⟩
    exact ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩
  exact
    ⟨chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsClosedWalkAnnulusBoundarySource,
      hcurrent,
      chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace,
      hwitness,
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_chainedDiamondsWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_chainedDiamondsWithTriangle,
      not_exists_taitEdgeColoring_chainedDiamondsWithTriangleGraph⟩

/-- The same chained-diamonds benchmark already reaches the exact one-collar current-boundary
shell and split-annulus witness assignment on a fixed honest source, and any hypothetical Tait
coloring would already close to full theorem-4.9 synthesis on that same embedding.  The actual
remaining blocker on this branch is therefore the absence of any Tait coloring, not missing
current-boundary or witness-assignment packaging. -/
theorem
    exists_closedWalkAnnulusBoundarySource_and_oneCollarAnnulusCurrentBoundaryData_and_facewiseAtMostOneInteriorEdge_and_annulusWitnessAssignment_and_theorem49BoundaryRootSynthesis_for_any_taitEdgeColoring_chainedDiamondsWithTriangleGraph_without_any_taitEdgeColoring
    [Fintype chainedDiamondsWithTriangleGraph.edgeSet]
    [FiniteDimensional F2 (chainedDiamondsWithTriangleGraph.edgeSet → Color)] :
    ∃ emb : PlaneEmbeddingWithBoundary chainedDiamondsWithTriangleGraph,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        (∃ data : PlanarBoundaryAnnulusCurrentBoundaryData emb,
          data.numCollars = 1 ∧
            data.toPlanarBoundaryAnnulusBoundaryData =
              source.toPlanarBoundaryAnnulusBoundaryData) ∧
        (∀ f : AmbientFace emb.faces,
          ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤
            (1 : ℕ)) ∧
        Nonempty
          (PlanarBoundaryAnnulusWitnessAssignment
            (planarBoundaryAnnulusDecomposition_of_boundaryData
              source.toPlanarBoundaryAnnulusBoundaryData)) ∧
        (∀ C : chainedDiamondsWithTriangleGraph.EdgeColoring Color,
          IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C →
            Theorem49BoundaryRootSynthesis emb C) ∧
        selectedBoundaryInteriorEdgeEndpointVertices emb = ∅ ∧
        ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty ∧
        ¬ ∃ C : chainedDiamondsWithTriangleGraph.EdgeColoring Color,
            IsTaitEdgeColoring chainedDiamondsWithTriangleGraph C := by
  have hcurrent :
      ∃ data : PlanarBoundaryAnnulusCurrentBoundaryData chainedDiamondsWithTriangleEmbedding,
        data.numCollars = 1 ∧
          data.toPlanarBoundaryAnnulusBoundaryData =
            chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData := by
    exact
      exists_oneCollarAnnulusCurrentBoundaryData_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        chainedDiamondsClosedWalkAnnulusBoundarySource
        chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace
  have hwitness :
      Nonempty
        (PlanarBoundaryAnnulusWitnessAssignment
          (planarBoundaryAnnulusDecomposition_of_boundaryData
            chainedDiamondsClosedWalkAnnulusBoundarySource.toPlanarBoundaryAnnulusBoundaryData)) := by
    rcases
      chainedDiamondsClosedWalkAnnulusBoundarySource_hasCanonicalWitnessChoice_via_atMostOneInteriorEdgePerFace
        with ⟨choice⟩
    exact ⟨choice.toPlanarBoundaryAnnulusWitnessAssignment⟩
  exact
    ⟨chainedDiamondsWithTriangleEmbedding,
      chainedDiamondsClosedWalkAnnulusBoundarySource,
      hcurrent,
      chainedDiamondsWithTriangle_atMostOneInteriorEdgePerFace,
      hwitness,
      (fun C hC =>
        chainedDiamondsWithTriangleEmbedding_theorem49BoundaryRootSynthesis_via_atMostOneInteriorEdgePerFace
          C hC),
      selectedBoundaryInteriorEdgeEndpointVertices_eq_empty_chainedDiamondsWithTriangle,
      not_selectedBoundaryInteriorEdgeEndpointVertices_nonempty_chainedDiamondsWithTriangle,
      not_exists_taitEdgeColoring_chainedDiamondsWithTriangleGraph⟩

end Theorem49PlanarBoundaryAnnulusHonestGeometryRegression

end Mettapedia.GraphTheory.FourColor
