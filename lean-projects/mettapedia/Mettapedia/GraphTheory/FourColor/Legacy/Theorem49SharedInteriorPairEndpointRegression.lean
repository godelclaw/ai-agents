import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
import Mettapedia.GraphTheory.FourColor.Theorem49Synthesis
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

namespace Theorem49SharedInteriorPairEndpointRegression

private noncomputable instance sharedInteriorPairAnnulusGraph_edgeSet_fintype :
    Fintype sharedInteriorPairAnnulusGraph.edgeSet :=
  Fintype.ofFinite _

private noncomputable def sharedInteriorPairBluePurpleOuterComponent :
    (sharedInteriorPairTaitEdgeColoring.bicoloredSubgraph blue purple).ConnectedComponent :=
  (sharedInteriorPairTaitEdgeColoring.bicoloredSubgraph blue purple).connectedComponentMk
    ⟨sip12, by
      left
      change sharedInteriorPairEdgeColor sip12 = blue
      simp⟩

private theorem sip12_adj_sip23 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip12 sip23 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (2 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip12, sip23] at this
  · simp [sip12]
  · simp [sip23]

private theorem sip23_adj_sip30 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip23 sip30 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (3 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip23, sip30] at this
  · simp [sip23]
  · simp [sip30]

private theorem sip30_adj_sip40 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip30 sip40 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (0 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip30, sip40] at this
  · simp [sip30]
  · simp [sip40]

private theorem sip12_mem_sharedInteriorPairBluePurpleOuterComponent :
    sip12 ∈ sharedInteriorPairTaitEdgeColoring.kempeComponentSet blue purple
      sharedInteriorPairBluePurpleOuterComponent := by
  exact sharedInteriorPairTaitEdgeColoring.mem_kempeComponentSet_self (by
    left
    change sharedInteriorPairEdgeColor sip12 = blue
    simp)

private theorem sip23_mem_sharedInteriorPairBluePurpleOuterComponent :
    sip23 ∈ sharedInteriorPairTaitEdgeColoring.kempeComponentSet blue purple
      sharedInteriorPairBluePurpleOuterComponent := by
  exact sharedInteriorPairTaitEdgeColoring.mem_kempeComponentSet_of_adj
    sip12_mem_sharedInteriorPairBluePurpleOuterComponent sip12_adj_sip23 (by
      right
      change sharedInteriorPairEdgeColor sip23 = purple
      simp)

private theorem sip30_mem_sharedInteriorPairBluePurpleOuterComponent :
    sip30 ∈ sharedInteriorPairTaitEdgeColoring.kempeComponentSet blue purple
      sharedInteriorPairBluePurpleOuterComponent := by
  exact sharedInteriorPairTaitEdgeColoring.mem_kempeComponentSet_of_adj
    sip23_mem_sharedInteriorPairBluePurpleOuterComponent sip23_adj_sip30 (by
      left
      change sharedInteriorPairEdgeColor sip30 = blue
      simp)

private theorem sip40_mem_sharedInteriorPairBluePurpleOuterComponent :
    sip40 ∈ sharedInteriorPairTaitEdgeColoring.kempeComponentSet blue purple
      sharedInteriorPairBluePurpleOuterComponent := by
  exact sharedInteriorPairTaitEdgeColoring.mem_kempeComponentSet_of_adj
    sip30_mem_sharedInteriorPairBluePurpleOuterComponent sip30_adj_sip40 (by
      right
      change sharedInteriorPairEdgeColor sip40 = purple
      simp)

private theorem sip01_not_mem_sharedInteriorPairBluePurpleOuterComponent :
    sip01 ∉ sharedInteriorPairTaitEdgeColoring.kempeComponentSet blue purple
      sharedInteriorPairBluePurpleOuterComponent := by
  intro hmem
  rcases sharedInteriorPairTaitEdgeColoring.mem_bicoloredSet_of_mem_kempeComponentSet hmem with
    hblue | hpurple
  · change sharedInteriorPairEdgeColor sip01 = blue at hblue
    simp at hblue
  · change sharedInteriorPairEdgeColor sip01 = purple at hpurple
    simp at hpurple

private theorem sip24_not_mem_sharedInteriorPairBluePurpleOuterComponent :
    sip24 ∉ sharedInteriorPairTaitEdgeColoring.kempeComponentSet blue purple
      sharedInteriorPairBluePurpleOuterComponent := by
  intro hmem
  rcases sharedInteriorPairTaitEdgeColoring.mem_bicoloredSet_of_mem_kempeComponentSet hmem with
    hblue | hpurple
  · change sharedInteriorPairEdgeColor sip24 = blue at hblue
    simp at hblue
  · change sharedInteriorPairEdgeColor sip24 = purple at hpurple
    simp at hpurple

private noncomputable def sharedInteriorPairBluePurpleOuterNeighbor :
    sharedInteriorPairAnnulusGraph.EdgeColoring Color :=
  sharedInteriorPairTaitEdgeColoring.swapOnKempeComponent blue purple
    sharedInteriorPairBluePurpleOuterComponent

private theorem sharedInteriorPairBluePurpleOuterNeighbor_mem_edgeKempeClosure :
    sharedInteriorPairBluePurpleOuterNeighbor ∈
      sharedInteriorPairAnnulusGraph.EdgeKempeClosure sharedInteriorPairTaitEdgeColoring := by
  exact sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_of_mem_of_step
    (sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
      sharedInteriorPairTaitEdgeColoring)
    blue purple sharedInteriorPairBluePurpleOuterComponent

@[simp] private theorem sharedInteriorPairBluePurpleOuterNeighbor_sip01 :
    sharedInteriorPairBluePurpleOuterNeighbor sip01 = red := by
  change (sharedInteriorPairTaitEdgeColoring.swapOnKempeComponent blue purple
    sharedInteriorPairBluePurpleOuterComponent) sip01 = red
  rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
  · change sharedInteriorPairEdgeColor sip01 = red
    simp
  · exact sip01_not_mem_sharedInteriorPairBluePurpleOuterComponent

@[simp] private theorem sharedInteriorPairBluePurpleOuterNeighbor_sip12 :
    sharedInteriorPairBluePurpleOuterNeighbor sip12 = purple := by
  change (sharedInteriorPairTaitEdgeColoring.swapOnKempeComponent blue purple
    sharedInteriorPairBluePurpleOuterComponent) sip12 = purple
  rw [Coloring.swapOnKempeComponent_apply_of_mem]
  · change Equiv.swap blue purple (sharedInteriorPairEdgeColor sip12) = purple
    simp
  · exact sip12_mem_sharedInteriorPairBluePurpleOuterComponent

@[simp] private theorem sharedInteriorPairBluePurpleOuterNeighbor_sip24 :
    sharedInteriorPairBluePurpleOuterNeighbor sip24 = red := by
  change (sharedInteriorPairTaitEdgeColoring.swapOnKempeComponent blue purple
    sharedInteriorPairBluePurpleOuterComponent) sip24 = red
  rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
  · change sharedInteriorPairEdgeColor sip24 = red
    simp
  · exact sip24_not_mem_sharedInteriorPairBluePurpleOuterComponent

@[simp] private theorem sharedInteriorPairBluePurpleOuterNeighbor_sip40 :
    sharedInteriorPairBluePurpleOuterNeighbor sip40 = blue := by
  change (sharedInteriorPairTaitEdgeColoring.swapOnKempeComponent blue purple
    sharedInteriorPairBluePurpleOuterComponent) sip40 = blue
  rw [Coloring.swapOnKempeComponent_apply_of_mem]
  · change Equiv.swap blue purple (sharedInteriorPairEdgeColor sip40) = blue
    simp
  · exact sip40_mem_sharedInteriorPairBluePurpleOuterComponent

private theorem face1_red_purple_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring red purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
      ({sip01, sip24, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem face1_red_blue_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
      ({sip01, sip12, sip24} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem face1_blue_purple_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring blue purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
      ({sip12, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem bluePurpleOuterNeighbor_face1_red_blue_support :
    boundaryBicoloredEdges sharedInteriorPairBluePurpleOuterNeighbor red blue
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
      ({sip01, sip24, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
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
      · simp [sharedInteriorPairBluePurpleOuterNeighbor_sip12, red, purple] at hred
      · simp [sharedInteriorPairBluePurpleOuterNeighbor_sip12, blue, purple] at hblue
    · simp
    · simp
  · intro h
    rcases Finset.mem_insert.1 h with rfl | h
    · exact ⟨by simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary], by simp⟩
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
    (hgen : AnnihilatesKempeClosureGeneratorFamily sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairTaitEdgeColoring z) :
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
            sharedInteriorPairTaitEdgeColoring)
          hgen
          (f := (1 : SharedInteriorPairFace))
          (e := sip01)
          (sharedInteriorPairTaitEdgeColoring_isTait sip01)
          blue blue_ne_zero (by
            change blue ≠ sharedInteriorPairEdgeColor sip01
            simp [red, blue])
      have hchain :
          chainDot ({sip01, sip24, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) z
            (indicatorChain blue ({sip01, sip24, sip40} :
              Finset sharedInteriorPairAnnulusGraph.edgeSet)) = 0 := by
        simpa [sharedInteriorPairTaitEdgeColoring, sharedInteriorPairEdgeColor_sip01,
          face1_red_purple_support,
          polarizedFaceGenerator_eq_indicatorChain_of_add_pair] using horth
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero (e := sip01) blue (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ sip01 := (Finset.mem_erase.1 he).1
        have hmem : e = sip01 ∨ e = sip24 ∨ e = sip40 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl | rfl
        · exact False.elim (hne rfl)
        · exact zero_on_sip24 hzeroBoundary
        · exact zero_on_sip40 hzeroBoundary
    · have horth :=
        localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
          (faceBoundary := sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (hC := sharedInteriorPairBluePurpleOuterNeighbor_mem_edgeKempeClosure)
          hgen
          (f := (1 : SharedInteriorPairFace))
          (e := sip01)
          (by simp)
          purple purple_ne_zero (by
            simp [sharedInteriorPairBluePurpleOuterNeighbor_sip01, red, purple])
      have horth' :
          chainDot
              (boundaryBicoloredEdges sharedInteriorPairBluePurpleOuterNeighbor red (red + purple)
                (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)))
              z
              (polarizedFaceGenerator sharedInteriorPairBluePurpleOuterNeighbor red (red + purple)
                (sharedInteriorPairAnnulusEmbedding.faceBoundary
                  (1 : SharedInteriorPairFace))) = 0 := by
        simpa [sharedInteriorPairBluePurpleOuterNeighbor_sip01] using horth
      have hpolarized :
          polarizedFaceGenerator sharedInteriorPairBluePurpleOuterNeighbor red (red + purple)
              (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
            indicatorChain purple
              (boundaryBicoloredEdges sharedInteriorPairBluePurpleOuterNeighbor red (red + purple)
                (sharedInteriorPairAnnulusEmbedding.faceBoundary
                  (1 : SharedInteriorPairFace))) := by
        simpa using polarizedFaceGenerator_eq_indicatorChain_of_add_pair
          sharedInteriorPairBluePurpleOuterNeighbor red purple
            (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace))
      have hsupport' :
          boundaryBicoloredEdges sharedInteriorPairBluePurpleOuterNeighbor red (red + purple)
              (sharedInteriorPairAnnulusEmbedding.faceBoundary (1 : SharedInteriorPairFace)) =
            ({sip01, sip24, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
        simpa [red, purple] using bluePurpleOuterNeighbor_face1_red_blue_support
      have hchain :
          chainDot ({sip01, sip24, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) z
            (indicatorChain purple ({sip01, sip24, sip40} :
              Finset sharedInteriorPairAnnulusGraph.edgeSet)) = 0 := by
        rw [hpolarized] at horth'
        rw [hsupport'] at horth'
        simpa using horth'
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero
        (e := sip01) purple (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ sip01 := (Finset.mem_erase.1 he).1
        have hmem : e = sip01 ∨ e = sip24 ∨ e = sip40 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl | rfl
        · exact False.elim (hne rfl)
        · exact zero_on_sip24 hzeroBoundary
        · exact zero_on_sip40 hzeroBoundary

private theorem zero_on_sip12_of_boundaryZero_and_annihilator
    {z : sharedInteriorPairAnnulusGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport sharedInteriorPairAnnulusEmbedding.faceBoundary
          sharedInteriorPairAnnulusEmbedding.faces sharedInteriorPairAnnulusEmbedding.faces,
        z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairTaitEdgeColoring z) :
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
            sharedInteriorPairTaitEdgeColoring)
          hgen
          (f := (1 : SharedInteriorPairFace))
          (e := sip12)
          (sharedInteriorPairTaitEdgeColoring_isTait sip12)
          red red_ne_zero (by
            change red ≠ sharedInteriorPairEdgeColor sip12
            simp [red, blue])
      have hchain :
          chainDot ({sip12, sip40} : Finset sharedInteriorPairAnnulusGraph.edgeSet) z
            (indicatorChain red ({sip12, sip40} :
              Finset sharedInteriorPairAnnulusGraph.edgeSet)) = 0 := by
        simpa [sharedInteriorPairTaitEdgeColoring, sharedInteriorPairEdgeColor_sip12,
          face1_blue_purple_support,
          polarizedFaceGenerator_eq_indicatorChain_of_add_pair] using horth
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero (e := sip12) red (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ sip12 := (Finset.mem_erase.1 he).1
        have hmem : e = sip12 ∨ e = sip40 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl
        · exact False.elim (hne rfl)
        · exact zero_on_sip40 hzeroBoundary
    · exact False.elim (hγne rfl)
    · have horth :=
        localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
          (faceBoundary := sharedInteriorPairAnnulusEmbedding.faceBoundary)
          (hC := sharedInteriorPairAnnulusGraph.mem_edgeKempeClosure_self
            sharedInteriorPairTaitEdgeColoring)
          hgen
          (f := (1 : SharedInteriorPairFace))
          (e := sip12)
          (sharedInteriorPairTaitEdgeColoring_isTait sip12)
          purple purple_ne_zero (by
            change purple ≠ sharedInteriorPairEdgeColor sip12
            simp [purple, blue])
      have hchain :
          chainDot ({sip01, sip12, sip24} : Finset sharedInteriorPairAnnulusGraph.edgeSet) z
            (indicatorChain purple ({sip01, sip12, sip24} :
              Finset sharedInteriorPairAnnulusGraph.edgeSet)) = 0 := by
        simpa [sharedInteriorPairTaitEdgeColoring, sharedInteriorPairEdgeColor_sip12,
          face1_red_blue_support,
          polarizedFaceGenerator_eq_indicatorChain_of_add_pair] using horth
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero
        (e := sip12) purple (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ sip12 := (Finset.mem_erase.1 he).1
        have hmem : e = sip01 ∨ e = sip12 ∨ e = sip24 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl | rfl
        · exact hsip01
        · exact False.elim (hne rfl)
        · exact zero_on_sip24 hzeroBoundary

/-- The shared-interior-pair benchmark satisfies the current endpoint directly for the explicit
Tait coloring after a single useful Kempe-neighbor check: every selected-boundary-zero chain
annihilating the radius-1 projected generators is forced to vanish on all nine edges. -/
theorem sharedInteriorPairAnnulusEmbedding_boundaryZeroAnnihilatorTrivial_for_explicitTaitColoring :
    BoundaryZeroAnnihilatorTrivialForEmbedding sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairTaitEdgeColoring := by
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

/-- Kernel-checked endpoint on the honest shared-interior-pair embedding for the explicit
benchmark coloring. This upgrades the former radius-1 lab certificate from computational evidence
to a Lean-checked theorem on the concrete benchmark. -/
theorem sharedInteriorPairAnnulusEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring
    [FiniteDimensional F2 (sharedInteriorPairAnnulusGraph.edgeSet → Color)] :
    Theorem49BoundaryRootSynthesis sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairTaitEdgeColoring := by
  exact theorem49BoundaryRootSynthesis_of_boundaryZeroAnnihilatorTrivial
    sharedInteriorPairTaitEdgeColoring
    sharedInteriorPairAnnulusEmbedding_boundaryZeroAnnihilatorTrivial_for_explicitTaitColoring

end Theorem49SharedInteriorPairEndpointRegression

end Mettapedia.GraphTheory.FourColor
