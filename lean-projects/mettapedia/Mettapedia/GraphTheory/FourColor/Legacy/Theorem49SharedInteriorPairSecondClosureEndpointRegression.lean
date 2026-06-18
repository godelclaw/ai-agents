import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
import Mettapedia.GraphTheory.FourColor.Theorem49Synthesis
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

namespace Theorem49SharedInteriorPairSecondClosureEndpointRegression

def sharedInteriorPairSecondClosureEdgeColor
    (e : sharedInteriorPairAnnulusGraph.edgeSet) : Color :=
  if e = sip01 ∨ e = sip23 ∨ e = sip56 then red
  else if e = sip12 ∨ e = sip40 ∨ e = sip67 then blue
  else purple

@[simp] private theorem sharedInteriorPairSecondClosureEdgeColor_sip01 :
    sharedInteriorPairSecondClosureEdgeColor sip01 = red := by
  simp [sharedInteriorPairSecondClosureEdgeColor]

@[simp] private theorem sharedInteriorPairSecondClosureEdgeColor_sip12 :
    sharedInteriorPairSecondClosureEdgeColor sip12 = blue := by
  simp [sharedInteriorPairSecondClosureEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip12,
    sip23, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairSecondClosureEdgeColor_sip23 :
    sharedInteriorPairSecondClosureEdgeColor sip23 = red := by
  simp [sharedInteriorPairSecondClosureEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip23]

@[simp] private theorem sharedInteriorPairSecondClosureEdgeColor_sip30 :
    sharedInteriorPairSecondClosureEdgeColor sip30 = purple := by
  simp [sharedInteriorPairSecondClosureEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip12,
    sip23, sip30, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairSecondClosureEdgeColor_sip24 :
    sharedInteriorPairSecondClosureEdgeColor sip24 = purple := by
  simp [sharedInteriorPairSecondClosureEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip12,
    sip23, sip24, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairSecondClosureEdgeColor_sip40 :
    sharedInteriorPairSecondClosureEdgeColor sip40 = blue := by
  simp [sharedInteriorPairSecondClosureEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip12,
    sip23, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairSecondClosureEdgeColor_sip56 :
    sharedInteriorPairSecondClosureEdgeColor sip56 = red := by
  simp [sharedInteriorPairSecondClosureEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip23,
    sip56]

@[simp] private theorem sharedInteriorPairSecondClosureEdgeColor_sip67 :
    sharedInteriorPairSecondClosureEdgeColor sip67 = blue := by
  simp [sharedInteriorPairSecondClosureEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip12,
    sip23, sip40, sip56, sip67]

@[simp] private theorem sharedInteriorPairSecondClosureEdgeColor_sip75 :
    sharedInteriorPairSecondClosureEdgeColor sip75 = purple := by
  simp [sharedInteriorPairSecondClosureEdgeColor, sharedInteriorPairAnnulusGraph, sip01, sip12,
    sip23, sip40, sip56, sip67, sip75]

def sharedInteriorPairSecondClosureTaitEdgeColoring :
    sharedInteriorPairAnnulusGraph.EdgeColoring Color :=
  Coloring.mk sharedInteriorPairSecondClosureEdgeColor (by
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
        simp [red, purple] at hne hcolor
    · rcases sharedInteriorPair_edge_mem_four he with rfl | rfl <;>
        rcases sharedInteriorPair_edge_mem_four hf with rfl | rfl <;>
        simp [blue, purple] at hne hcolor
    · rcases sharedInteriorPair_edge_mem_five he with rfl | rfl <;>
        rcases sharedInteriorPair_edge_mem_five hf with rfl | rfl <;>
        simp [red, purple] at hne hcolor
    · rcases sharedInteriorPair_edge_mem_six he with rfl | rfl <;>
        rcases sharedInteriorPair_edge_mem_six hf with rfl | rfl <;>
        simp [red, blue] at hne hcolor
    · rcases sharedInteriorPair_edge_mem_seven he with rfl | rfl <;>
        rcases sharedInteriorPair_edge_mem_seven hf with rfl | rfl <;>
        simp [blue, purple] at hne hcolor)

theorem sharedInteriorPairSecondClosureTaitEdgeColoring_isTait :
    IsTaitEdgeColoring sharedInteriorPairAnnulusGraph
      sharedInteriorPairSecondClosureTaitEdgeColoring := by
  intro e
  change sharedInteriorPairSecondClosureEdgeColor e ≠ 0
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

private noncomputable instance sharedInteriorPairAnnulusGraph_edgeSet_fintype :
    Fintype sharedInteriorPairAnnulusGraph.edgeSet :=
  Fintype.ofFinite _

private noncomputable def sharedInteriorPairSecondClosureBluePurpleInnerComponent :
    (sharedInteriorPairSecondClosureTaitEdgeColoring.bicoloredSubgraph blue purple).ConnectedComponent :=
  (sharedInteriorPairSecondClosureTaitEdgeColoring.bicoloredSubgraph blue purple).connectedComponentMk
    ⟨sip12, by
      left
      change sharedInteriorPairSecondClosureEdgeColor sip12 = blue
      simp⟩

private theorem sip12_adj_sip24 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip12 sip24 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (2 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip12, sip24] at this
  · simp [sip12]
  · simp [sip24]

private theorem sip24_adj_sip40 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip24 sip40 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (4 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip24, sip40] at this
  · simp [sip24]
  · simp [sip40]

private theorem sip40_adj_sip30 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip40 sip30 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (0 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip40, sip30] at this
  · simp [sip40]
  · simp [sip30]

private theorem sip12_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent :
    sip12 ∈ sharedInteriorPairSecondClosureTaitEdgeColoring.kempeComponentSet blue purple
      sharedInteriorPairSecondClosureBluePurpleInnerComponent := by
  exact sharedInteriorPairSecondClosureTaitEdgeColoring.mem_kempeComponentSet_self (by
    left
    change sharedInteriorPairSecondClosureEdgeColor sip12 = blue
    simp)

private theorem sip24_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent :
    sip24 ∈ sharedInteriorPairSecondClosureTaitEdgeColoring.kempeComponentSet blue purple
      sharedInteriorPairSecondClosureBluePurpleInnerComponent := by
  exact sharedInteriorPairSecondClosureTaitEdgeColoring.mem_kempeComponentSet_of_adj
    sip12_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent sip12_adj_sip24 (by
      right
      change sharedInteriorPairSecondClosureEdgeColor sip24 = purple
      simp)

private theorem sip40_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent :
    sip40 ∈ sharedInteriorPairSecondClosureTaitEdgeColoring.kempeComponentSet blue purple
      sharedInteriorPairSecondClosureBluePurpleInnerComponent := by
  exact sharedInteriorPairSecondClosureTaitEdgeColoring.mem_kempeComponentSet_of_adj
    sip24_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent sip24_adj_sip40 (by
      left
      change sharedInteriorPairSecondClosureEdgeColor sip40 = blue
      simp)

private theorem sip30_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent :
    sip30 ∈ sharedInteriorPairSecondClosureTaitEdgeColoring.kempeComponentSet blue purple
      sharedInteriorPairSecondClosureBluePurpleInnerComponent := by
  exact sharedInteriorPairSecondClosureTaitEdgeColoring.mem_kempeComponentSet_of_adj
    sip40_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent sip40_adj_sip30 (by
      right
      change sharedInteriorPairSecondClosureEdgeColor sip30 = purple
      simp)

private theorem sip01_not_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent :
    sip01 ∉ sharedInteriorPairSecondClosureTaitEdgeColoring.kempeComponentSet blue purple
      sharedInteriorPairSecondClosureBluePurpleInnerComponent := by
  intro hmem
  rcases sharedInteriorPairSecondClosureTaitEdgeColoring.mem_bicoloredSet_of_mem_kempeComponentSet
      hmem with hblue | hpurple
  · change sharedInteriorPairSecondClosureEdgeColor sip01 = blue at hblue
    simp at hblue
  · change sharedInteriorPairSecondClosureEdgeColor sip01 = purple at hpurple
    simp at hpurple

private theorem sip23_not_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent :
    sip23 ∉ sharedInteriorPairSecondClosureTaitEdgeColoring.kempeComponentSet blue purple
      sharedInteriorPairSecondClosureBluePurpleInnerComponent := by
  intro hmem
  rcases sharedInteriorPairSecondClosureTaitEdgeColoring.mem_bicoloredSet_of_mem_kempeComponentSet
      hmem with hblue | hpurple
  · change sharedInteriorPairSecondClosureEdgeColor sip23 = blue at hblue
    simp at hblue
  · change sharedInteriorPairSecondClosureEdgeColor sip23 = purple at hpurple
    simp at hpurple

private noncomputable def sharedInteriorPairSecondClosureBluePurpleInnerNeighbor :
    sharedInteriorPairAnnulusGraph.EdgeColoring Color :=
  sharedInteriorPairSecondClosureTaitEdgeColoring.swapOnKempeComponent blue purple
    sharedInteriorPairSecondClosureBluePurpleInnerComponent

private theorem sharedInteriorPairSecondClosureBluePurpleInnerNeighbor_mem_edgeKempeClosure :
    sharedInteriorPairSecondClosureBluePurpleInnerNeighbor ∈
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure
        sharedInteriorPairSecondClosureTaitEdgeColoring := by
  exact sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_of_mem_of_step
    (sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
      sharedInteriorPairSecondClosureTaitEdgeColoring)
    blue purple sharedInteriorPairSecondClosureBluePurpleInnerComponent

@[simp] private theorem sharedInteriorPairSecondClosureBluePurpleInnerNeighbor_sip01 :
    sharedInteriorPairSecondClosureBluePurpleInnerNeighbor sip01 = red := by
  change (sharedInteriorPairSecondClosureTaitEdgeColoring.swapOnKempeComponent blue purple
    sharedInteriorPairSecondClosureBluePurpleInnerComponent) sip01 = red
  rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
  · change sharedInteriorPairSecondClosureEdgeColor sip01 = red
    simp
  · exact sip01_not_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent

@[simp] private theorem sharedInteriorPairSecondClosureBluePurpleInnerNeighbor_sip12 :
    sharedInteriorPairSecondClosureBluePurpleInnerNeighbor sip12 = purple := by
  change (sharedInteriorPairSecondClosureTaitEdgeColoring.swapOnKempeComponent blue purple
    sharedInteriorPairSecondClosureBluePurpleInnerComponent) sip12 = purple
  rw [Coloring.swapOnKempeComponent_apply_of_mem]
  · change Equiv.swap blue purple (sharedInteriorPairSecondClosureEdgeColor sip12) = purple
    simp
  · exact sip12_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent

@[simp] private theorem sharedInteriorPairSecondClosureBluePurpleInnerNeighbor_sip24 :
    sharedInteriorPairSecondClosureBluePurpleInnerNeighbor sip24 = blue := by
  change (sharedInteriorPairSecondClosureTaitEdgeColoring.swapOnKempeComponent blue purple
    sharedInteriorPairSecondClosureBluePurpleInnerComponent) sip24 = blue
  rw [Coloring.swapOnKempeComponent_apply_of_mem]
  · change Equiv.swap blue purple (sharedInteriorPairSecondClosureEdgeColor sip24) = blue
    simp
  · exact sip24_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent

@[simp] private theorem sharedInteriorPairSecondClosureBluePurpleInnerNeighbor_sip40 :
    sharedInteriorPairSecondClosureBluePurpleInnerNeighbor sip40 = purple := by
  change (sharedInteriorPairSecondClosureTaitEdgeColoring.swapOnKempeComponent blue purple
    sharedInteriorPairSecondClosureBluePurpleInnerComponent) sip40 = purple
  rw [Coloring.swapOnKempeComponent_apply_of_mem]
  · change Equiv.swap blue purple (sharedInteriorPairSecondClosureEdgeColor sip40) = purple
    simp
  · exact sip40_mem_sharedInteriorPairSecondClosureBluePurpleInnerComponent

private theorem face1_red_purple_support :
    boundaryBicoloredEdges sharedInteriorPairSecondClosureTaitEdgeColoring red purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
      ({sip01, sip24} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem face1_red_blue_support :
    boundaryBicoloredEdges sharedInteriorPairSecondClosureTaitEdgeColoring red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
      ({sip01, sip12, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem face1_blue_purple_support :
    boundaryBicoloredEdges sharedInteriorPairSecondClosureTaitEdgeColoring blue purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
      ({sip12, sip24, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem bluePurpleInnerNeighbor_face1_red_blue_support :
    boundaryBicoloredEdges sharedInteriorPairSecondClosureBluePurpleInnerNeighbor red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
      ({sip01, sip24} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  apply Finset.ext
  intro e
  rw [mem_boundaryBicoloredEdges_iff]
  constructor
  · intro h
    rcases h with ⟨hface, hcolor⟩
    have hface' : e = sip01 ∨ e = sip12 ∨ e = sip24 ∨ e = sip40 := by
      simpa [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary] using hface
    rcases hface' with rfl | rfl | rfl | rfl
    · simp
    · rcases hcolor with hred | hblue
      · simp [sharedInteriorPairSecondClosureBluePurpleInnerNeighbor_sip12, red, purple] at hred
      · simp [sharedInteriorPairSecondClosureBluePurpleInnerNeighbor_sip12, blue, purple] at hblue
    · simp
    · rcases hcolor with hred | hblue
      · simp [sharedInteriorPairSecondClosureBluePurpleInnerNeighbor_sip40, red, purple] at hred
      · simp [sharedInteriorPairSecondClosureBluePurpleInnerNeighbor_sip40, blue, purple] at hblue
  · intro h
    rcases Finset.mem_insert.1 h with rfl | h
    · exact ⟨by simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary], by simp⟩
    rcases Finset.mem_singleton.1 h
    exact ⟨by simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary], by simp⟩

private theorem zero_on_sip23 {z : sharedInteriorPairAnnulusGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces sharedInteriorPairAnnulusEmbedding.faces,
        z e = 0) :
    z sip23 = 0 :=
  hzeroBoundary sip23 sip23_mem_selectedBoundarySupport

private theorem zero_on_sip24 {z : sharedInteriorPairAnnulusGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces sharedInteriorPairAnnulusEmbedding.faces,
        z e = 0) :
    z sip24 = 0 :=
  hzeroBoundary sip24 sip24_mem_selectedBoundarySupport

private theorem zero_on_sip30 {z : sharedInteriorPairAnnulusGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces sharedInteriorPairAnnulusEmbedding.faces,
        z e = 0) :
    z sip30 = 0 :=
  hzeroBoundary sip30 sip30_mem_selectedBoundarySupport

private theorem zero_on_sip40 {z : sharedInteriorPairAnnulusGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces sharedInteriorPairAnnulusEmbedding.faces,
        z e = 0) :
    z sip40 = 0 :=
  hzeroBoundary sip40 sip40_mem_selectedBoundarySupport

private theorem zero_on_sip56 {z : sharedInteriorPairAnnulusGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces sharedInteriorPairAnnulusEmbedding.faces,
        z e = 0) :
    z sip56 = 0 :=
  hzeroBoundary sip56 sip56_mem_selectedBoundarySupport

private theorem zero_on_sip67 {z : sharedInteriorPairAnnulusGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces sharedInteriorPairAnnulusEmbedding.faces,
        z e = 0) :
    z sip67 = 0 :=
  hzeroBoundary sip67 sip67_mem_selectedBoundarySupport

private theorem zero_on_sip75 {z : sharedInteriorPairAnnulusGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces sharedInteriorPairAnnulusEmbedding.faces,
        z e = 0) :
    z sip75 = 0 :=
  hzeroBoundary sip75 sip75_mem_selectedBoundarySupport

private theorem zero_on_sip01_of_boundaryZero_and_annihilator
    {z : sharedInteriorPairAnnulusGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces sharedInteriorPairAnnulusEmbedding.faces,
        z e = 0)
    (hgen :
      AnnihilatesKempeClosureGeneratorFamily sharedInteriorPairAnnulusEmbedding.faceBoundary
        sharedInteriorPairSecondClosureTaitEdgeColoring z) :
    z sip01 = 0 := by
  apply eq_zero_of_colorDot_eq_zero_for_all_nonzero_ne (z := z sip01) (d := red)
  · exact red_ne_zero
  · intro γ hγ0 hγne
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero γ hγ0 with rfl | rfl | rfl
    · exact False.elim (hγne rfl)
    · have horth :=
        localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
          (faceBoundary := sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (hC := sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
            sharedInteriorPairSecondClosureTaitEdgeColoring)
          hgen
          (f := (1 : SharedInteriorPairFace))
          (e := sip01)
          (sharedInteriorPairSecondClosureTaitEdgeColoring_isTait sip01)
          blue blue_ne_zero (by
            change blue ≠ sharedInteriorPairSecondClosureEdgeColor sip01
            simp [red, blue])
      have hchain :
          chainDot ({sip01, sip24} : Finset sharedInteriorPairAnnulusGraph.edgeSet) z
            (indicatorChain blue ({sip01, sip24} :
              Finset sharedInteriorPairAnnulusGraph.edgeSet)) = 0 := by
        simpa [sharedInteriorPairSecondClosureTaitEdgeColoring,
          sharedInteriorPairSecondClosureEdgeColor_sip01, face1_red_purple_support,
          polarizedFaceGenerator_eq_indicatorChain_of_add_pair] using horth
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero (e := sip01) blue (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ sip01 := (Finset.mem_erase.1 he).1
        have hmem : e = sip01 ∨ e = sip24 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl
        · exact False.elim (hne rfl)
        · exact zero_on_sip24 hzeroBoundary
    · have horth :=
        localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
          (faceBoundary := sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (hC := sharedInteriorPairSecondClosureBluePurpleInnerNeighbor_mem_edgeKempeClosure)
          hgen
          (f := (1 : SharedInteriorPairFace))
          (e := sip01)
          (by simp)
          purple purple_ne_zero (by
            simp [sharedInteriorPairSecondClosureBluePurpleInnerNeighbor_sip01, red, purple])
      have horth' :
          chainDot
              (boundaryBicoloredEdges sharedInteriorPairSecondClosureBluePurpleInnerNeighbor red
                (red + purple)
                (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)))
              z
              (polarizedFaceGenerator sharedInteriorPairSecondClosureBluePurpleInnerNeighbor red
                (red + purple)
                (sharedInteriorPairAnnulusEmbedding.faceBoundary
                  (1 : SharedInteriorPairFace))) = 0 := by
        simpa [sharedInteriorPairSecondClosureBluePurpleInnerNeighbor_sip01] using horth
      have hpolarized :
          polarizedFaceGenerator sharedInteriorPairSecondClosureBluePurpleInnerNeighbor red
              (red + purple)
              (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
            indicatorChain purple
              (boundaryBicoloredEdges sharedInteriorPairSecondClosureBluePurpleInnerNeighbor red
                (red + purple)
                (sharedInteriorPairAnnulusEmbedding.faceBoundary
                  (1 : SharedInteriorPairFace))) := by
        simpa using polarizedFaceGenerator_eq_indicatorChain_of_add_pair
          sharedInteriorPairSecondClosureBluePurpleInnerNeighbor red purple
            (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace))
      have hsupport' :
          boundaryBicoloredEdges sharedInteriorPairSecondClosureBluePurpleInnerNeighbor red
              (red + purple)
              (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
            ({sip01, sip24} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
        simpa [red, purple] using bluePurpleInnerNeighbor_face1_red_blue_support
      have hchain :
          chainDot ({sip01, sip24} : Finset sharedInteriorPairAnnulusGraph.edgeSet) z
            (indicatorChain purple ({sip01, sip24} :
              Finset sharedInteriorPairAnnulusGraph.edgeSet)) = 0 := by
        rw [hpolarized] at horth'
        rw [hsupport'] at horth'
        simpa using horth'
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero
        (e := sip01) purple (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ sip01 := (Finset.mem_erase.1 he).1
        have hmem : e = sip01 ∨ e = sip24 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl
        · exact False.elim (hne rfl)
        · exact zero_on_sip24 hzeroBoundary

private theorem zero_on_sip12_of_boundaryZero_and_annihilator
    {z : sharedInteriorPairAnnulusGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces sharedInteriorPairAnnulusEmbedding.faces,
        z e = 0)
    (hgen :
      AnnihilatesKempeClosureGeneratorFamily sharedInteriorPairAnnulusEmbedding.faceBoundary
        sharedInteriorPairSecondClosureTaitEdgeColoring z) :
    z sip12 = 0 := by
  have hsip01 : z sip01 = 0 :=
    zero_on_sip01_of_boundaryZero_and_annihilator hzeroBoundary hgen
  apply eq_zero_of_colorDot_eq_zero_for_all_nonzero_ne (z := z sip12) (d := blue)
  · exact blue_ne_zero
  · intro γ hγ0 hγne
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero γ hγ0 with rfl | rfl | rfl
    · have horth :=
        localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
          (faceBoundary := sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (hC := sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
            sharedInteriorPairSecondClosureTaitEdgeColoring)
          hgen
          (f := (1 : SharedInteriorPairFace))
          (e := sip12)
          (sharedInteriorPairSecondClosureTaitEdgeColoring_isTait sip12)
          red red_ne_zero (by
            change red ≠ sharedInteriorPairSecondClosureEdgeColor sip12
            simp [red, blue])
      have hchain :
          chainDot ({sip12, sip24, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) z
            (indicatorChain red ({sip12, sip24, sip40} :
              Finset sharedInteriorPairAnnulusGraph.edgeSet)) = 0 := by
        simpa [sharedInteriorPairSecondClosureTaitEdgeColoring,
          sharedInteriorPairSecondClosureEdgeColor_sip12, face1_blue_purple_support,
          polarizedFaceGenerator_eq_indicatorChain_of_add_pair] using horth
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero (e := sip12) red (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ sip12 := (Finset.mem_erase.1 he).1
        have hmem : e = sip12 ∨ e = sip24 ∨ e = sip40 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl | rfl
        · exact False.elim (hne rfl)
        · exact zero_on_sip24 hzeroBoundary
        · exact zero_on_sip40 hzeroBoundary
    · exact False.elim (hγne rfl)
    · have horth :=
        localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
          (faceBoundary := sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (hC := sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
            sharedInteriorPairSecondClosureTaitEdgeColoring)
          hgen
          (f := (1 : SharedInteriorPairFace))
          (e := sip12)
          (sharedInteriorPairSecondClosureTaitEdgeColoring_isTait sip12)
          purple purple_ne_zero (by
            change purple ≠ sharedInteriorPairSecondClosureEdgeColor sip12
            simp [purple, blue])
      have hchain :
          chainDot ({sip01, sip12, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) z
            (indicatorChain purple ({sip01, sip12, sip40} :
              Finset sharedInteriorPairAnnulusGraph.edgeSet)) = 0 := by
        simpa [sharedInteriorPairSecondClosureTaitEdgeColoring,
          sharedInteriorPairSecondClosureEdgeColor_sip12, face1_red_blue_support,
          polarizedFaceGenerator_eq_indicatorChain_of_add_pair] using horth
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero
        (e := sip12) purple (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ sip12 := (Finset.mem_erase.1 he).1
        have hmem : e = sip01 ∨ e = sip12 ∨ e = sip40 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl | rfl
        · exact hsip01
        · exact False.elim (hne rfl)
        · exact zero_on_sip40 hzeroBoundary

/-- The second Kempe-closure class on the shared-interior-pair benchmark also satisfies the
current endpoint directly: one useful radius-1 blue/purple neighbor already forces every
selected-boundary-zero annihilator to vanish on all nine edges. -/
theorem sharedInteriorPairAnnulusEmbedding_boundaryZeroAnnihilatorTrivial_for_secondClosureTaitColoring :
    BoundaryZeroAnnihilatorTrivialForEmbedding sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairSecondClosureTaitEdgeColoring := by
  intro z hzeroBoundary hgen e
  have hsip01 : z sip01 = 0 :=
    zero_on_sip01_of_boundaryZero_and_annihilator hzeroBoundary hgen
  have hsip12 : z sip12 = 0 :=
    zero_on_sip12_of_boundaryZero_and_annihilator hzeroBoundary hgen
  have hsip23 : z sip23 = 0 := zero_on_sip23 hzeroBoundary
  have hsip24 : z sip24 = 0 := zero_on_sip24 hzeroBoundary
  have hsip30 : z sip30 = 0 := zero_on_sip30 hzeroBoundary
  have hsip40 : z sip40 = 0 := zero_on_sip40 hzeroBoundary
  have hsip56 : z sip56 = 0 := zero_on_sip56 hzeroBoundary
  have hsip67 : z sip67 = 0 := zero_on_sip67 hzeroBoundary
  have hsip75 : z sip75 = 0 := zero_on_sip75 hzeroBoundary
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

/-- Kernel-checked endpoint on the honest shared-interior-pair embedding for a representative of
the second Kempe-closure class among its Tait colorings. -/
theorem sharedInteriorPairAnnulusEmbedding_theorem49BoundaryRootSynthesis_for_secondClosureTaitColoring
    [FiniteDimensional F2 (sharedInteriorPairAnnulusGraph.edgeSet → Color)] :
    Theorem49BoundaryRootSynthesis sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairSecondClosureTaitEdgeColoring := by
  exact theorem49BoundaryRootSynthesis_of_boundaryZeroAnnihilatorTrivial
    sharedInteriorPairSecondClosureTaitEdgeColoring
    sharedInteriorPairAnnulusEmbedding_boundaryZeroAnnihilatorTrivial_for_secondClosureTaitColoring

end Theorem49SharedInteriorPairSecondClosureEndpointRegression

end Mettapedia.GraphTheory.FourColor
