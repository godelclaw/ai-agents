import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorCoordinateDetector
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusHonestWitnessRegression
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49PlanarBoundaryAnnulusHonestWitnessRegression

namespace Theorem49SharedInteriorPairRadiusOneDetectorRegression

private noncomputable instance sharedInteriorPairAnnulusGraph_edgeSet_fintype :
    Fintype sharedInteriorPairAnnulusGraph.edgeSet :=
  Fintype.ofFinite _

attribute [simp] sip23_mem_selectedBoundarySupport
attribute [simp] sip30_mem_selectedBoundarySupport
attribute [simp] sip24_mem_selectedBoundarySupport
attribute [simp] sip40_mem_selectedBoundarySupport
attribute [simp] sip56_mem_selectedBoundarySupport
attribute [simp] sip67_mem_selectedBoundarySupport
attribute [simp] sip75_mem_selectedBoundarySupport
attribute [simp] sip01_not_mem_selectedBoundarySupport
attribute [simp] sip12_not_mem_selectedBoundarySupport

private theorem validColorPair_red_blue : ValidColorPair red blue :=
  ⟨red_ne_zero, blue_ne_zero, red_ne_blue⟩

private theorem validColorPair_red_purple : ValidColorPair red purple :=
  ⟨red_ne_zero, purple_ne_zero, red_ne_purple⟩

private theorem validColorPair_blue_purple : ValidColorPair blue purple :=
  ⟨blue_ne_zero, purple_ne_zero, blue_ne_purple⟩

private def sharedInteriorPairSelectedBoundaryProjection :
    (sharedInteriorPairAnnulusGraph.edgeSet → Color) →ₗ[F2]
      (sharedInteriorPairAnnulusGraph.edgeSet → Color) :=
  boundaryZeroProjection
    (selectedBoundarySupport
      sharedInteriorPairAnnulusEmbedding.faceBoundary
      sharedInteriorPairAnnulusEmbedding.faces
      sharedInteriorPairAnnulusEmbedding.faces)

private theorem sip01_adj_sip12 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip01 sip12 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (1 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip01, sip12] at this
  · simp [sip01]
  · simp [sip12]

private theorem sip12_adj_sip24 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip12 sip24 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (2 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip12, sip24] at this
  · simp [sip12]
  · simp [sip24]

private theorem sip01_adj_sip30 :
    sharedInteriorPairAnnulusGraph.lineGraph.Adj sip01 sip30 := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  refine ⟨?_, (0 : Fin 8), ?_, ?_⟩
  · intro h
    have := congrArg Subtype.val h
    simp [sip01, sip30] at this
  · simp [sip01]
  · simp [sip30]

private noncomputable def sharedInteriorPairRedBlueInnerComponent :
    (sharedInteriorPairTaitEdgeColoring.bicoloredSubgraph red blue).ConnectedComponent :=
  (sharedInteriorPairTaitEdgeColoring.bicoloredSubgraph red blue).connectedComponentMk
    ⟨sip01, by
      left
      change sharedInteriorPairEdgeColor sip01 = red
      simp⟩

private theorem sip01_mem_sharedInteriorPairRedBlueInnerComponent :
    sip01 ∈ sharedInteriorPairTaitEdgeColoring.kempeComponentSet red blue
      sharedInteriorPairRedBlueInnerComponent := by
  exact sharedInteriorPairTaitEdgeColoring.mem_kempeComponentSet_self (by
    left
    change sharedInteriorPairEdgeColor sip01 = red
    simp)

private theorem sip12_mem_sharedInteriorPairRedBlueInnerComponent :
    sip12 ∈ sharedInteriorPairTaitEdgeColoring.kempeComponentSet red blue
      sharedInteriorPairRedBlueInnerComponent := by
  exact sharedInteriorPairTaitEdgeColoring.mem_kempeComponentSet_of_adj
    sip01_mem_sharedInteriorPairRedBlueInnerComponent sip01_adj_sip12 (by
      right
      change sharedInteriorPairEdgeColor sip12 = blue
      simp)

private theorem sip24_mem_sharedInteriorPairRedBlueInnerComponent :
    sip24 ∈ sharedInteriorPairTaitEdgeColoring.kempeComponentSet red blue
      sharedInteriorPairRedBlueInnerComponent := by
  exact sharedInteriorPairTaitEdgeColoring.mem_kempeComponentSet_of_adj
    sip12_mem_sharedInteriorPairRedBlueInnerComponent sip12_adj_sip24 (by
      left
      change sharedInteriorPairEdgeColor sip24 = red
      simp)

private theorem sip30_mem_sharedInteriorPairRedBlueInnerComponent :
    sip30 ∈ sharedInteriorPairTaitEdgeColoring.kempeComponentSet red blue
      sharedInteriorPairRedBlueInnerComponent := by
  exact sharedInteriorPairTaitEdgeColoring.mem_kempeComponentSet_of_adj
    sip01_mem_sharedInteriorPairRedBlueInnerComponent sip01_adj_sip30 (by
      right
      change sharedInteriorPairEdgeColor sip30 = blue
      simp)

private theorem sip23_not_mem_sharedInteriorPairRedBlueInnerComponent :
    sip23 ∉ sharedInteriorPairTaitEdgeColoring.kempeComponentSet red blue
      sharedInteriorPairRedBlueInnerComponent := by
  intro hmem
  rcases sharedInteriorPairTaitEdgeColoring.mem_bicoloredSet_of_mem_kempeComponentSet hmem with
    hred | hblue
  · change sharedInteriorPairEdgeColor sip23 = red at hred
    simp [sharedInteriorPairEdgeColor_sip23, purple, red] at hred
  · change sharedInteriorPairEdgeColor sip23 = blue at hblue
    simp [sharedInteriorPairEdgeColor_sip23, purple, blue] at hblue

private noncomputable def sharedInteriorPairInnerRedBlueNeighbor :
    sharedInteriorPairAnnulusGraph.EdgeColoring Color :=
  sharedInteriorPairTaitEdgeColoring.swapOnKempeComponent red blue
    sharedInteriorPairRedBlueInnerComponent

private theorem sharedInteriorPairInnerRedBlueNeighbor_mem_radiusOne :
    sharedInteriorPairInnerRedBlueNeighbor ∈
      {C : sharedInteriorPairAnnulusGraph.EdgeColoring Color |
        ∃ a b : Color, ValidColorPair a b ∧
          ∃ K : (sharedInteriorPairTaitEdgeColoring.bicoloredSubgraph a b).ConnectedComponent,
            C = sharedInteriorPairTaitEdgeColoring.swapOnKempeComponent a b K} := by
  refine ⟨red, blue, validColorPair_red_blue, sharedInteriorPairRedBlueInnerComponent, rfl⟩

/-- The exact radius-1 Kempe neighborhood around the explicit shared coloring: the base coloring
plus all one-step swaps on valid color-pair components.  The preserved finite lab reports that
this set has seven distinct colorings on the shared benchmark. -/
private def sharedInteriorPairRadiusOneColorings :
    Set (sharedInteriorPairAnnulusGraph.EdgeColoring Color) :=
  {C | C = sharedInteriorPairTaitEdgeColoring ∨
      ∃ a b : Color, ValidColorPair a b ∧
        ∃ K : (sharedInteriorPairTaitEdgeColoring.bicoloredSubgraph a b).ConnectedComponent,
          C = sharedInteriorPairTaitEdgeColoring.swapOnKempeComponent a b K}

/-- A smaller witness subfamily already suffices for the detector: the explicit coloring together
with the single inner red/blue swap. -/
private def sharedInteriorPairRadiusOneWitnessColorings :
    Set (sharedInteriorPairAnnulusGraph.EdgeColoring Color) :=
  {C | C = sharedInteriorPairTaitEdgeColoring ∨ C = sharedInteriorPairInnerRedBlueNeighbor}

private theorem sharedInteriorPairRadiusOneWitnessColorings_subset_radiusOne :
    sharedInteriorPairRadiusOneWitnessColorings ⊆
      sharedInteriorPairRadiusOneColorings := by
  intro C hC
  rcases hC with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr sharedInteriorPairInnerRedBlueNeighbor_mem_radiusOne

@[simp] private theorem sharedInteriorPairInnerRedBlueNeighbor_sip01 :
    sharedInteriorPairInnerRedBlueNeighbor sip01 = blue := by
  change (sharedInteriorPairTaitEdgeColoring.swapOnKempeComponent red blue
    sharedInteriorPairRedBlueInnerComponent) sip01 = blue
  rw [Coloring.swapOnKempeComponent_apply_of_mem]
  · change Equiv.swap red blue (sharedInteriorPairEdgeColor sip01) = blue
    simp
  · exact sip01_mem_sharedInteriorPairRedBlueInnerComponent

@[simp] private theorem sharedInteriorPairInnerRedBlueNeighbor_sip12 :
    sharedInteriorPairInnerRedBlueNeighbor sip12 = red := by
  change (sharedInteriorPairTaitEdgeColoring.swapOnKempeComponent red blue
    sharedInteriorPairRedBlueInnerComponent) sip12 = red
  rw [Coloring.swapOnKempeComponent_apply_of_mem]
  · change Equiv.swap red blue (sharedInteriorPairEdgeColor sip12) = red
    simp
  · exact sip12_mem_sharedInteriorPairRedBlueInnerComponent

@[simp] private theorem sharedInteriorPairInnerRedBlueNeighbor_sip23 :
    sharedInteriorPairInnerRedBlueNeighbor sip23 = purple := by
  change (sharedInteriorPairTaitEdgeColoring.swapOnKempeComponent red blue
    sharedInteriorPairRedBlueInnerComponent) sip23 = purple
  rw [Coloring.swapOnKempeComponent_apply_of_not_mem]
  · change sharedInteriorPairEdgeColor sip23 = purple
    simp
  · exact sip23_not_mem_sharedInteriorPairRedBlueInnerComponent

@[simp] private theorem sharedInteriorPairInnerRedBlueNeighbor_sip30 :
    sharedInteriorPairInnerRedBlueNeighbor sip30 = red := by
  change (sharedInteriorPairTaitEdgeColoring.swapOnKempeComponent red blue
    sharedInteriorPairRedBlueInnerComponent) sip30 = red
  rw [Coloring.swapOnKempeComponent_apply_of_mem]
  · change Equiv.swap red blue (sharedInteriorPairEdgeColor sip30) = red
    simp
  · exact sip30_mem_sharedInteriorPairRedBlueInnerComponent

private theorem explicit_face0_red_purple_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring red purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace)) =
      ({sip01, sip23} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem explicit_face0_blue_purple_support :
    boundaryBicoloredEdges sharedInteriorPairTaitEdgeColoring blue purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace)) =
      ({sip12, sip23, sip30} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  decide

private theorem innerRedBlue_face0_red_purple_support :
    boundaryBicoloredEdges sharedInteriorPairInnerRedBlueNeighbor red purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace)) =
      ({sip12, sip23, sip30} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  apply Finset.ext
  intro e
  rw [mem_boundaryBicoloredEdges_iff]
  constructor
  · intro h
    rcases h with ⟨hface, hcolor⟩
    have hface' : e = sip01 ∨ e = sip12 ∨ e = sip23 ∨ e = sip30 := by
      simpa [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary] using hface
    rcases hface' with rfl | rfl | rfl | rfl
    · rcases hcolor with hred | hpurple
      · simp [sharedInteriorPairInnerRedBlueNeighbor_sip01, red, blue] at hred
      · simp [sharedInteriorPairInnerRedBlueNeighbor_sip01, purple, blue] at hpurple
    · simp
    · simp
    · simp
  · intro h
    rcases Finset.mem_insert.1 h with rfl | h
    · exact ⟨by simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary], by simp⟩
    rcases Finset.mem_insert.1 h with rfl | h
    · exact ⟨by simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary], by simp⟩
    rcases Finset.mem_singleton.1 h
    exact ⟨by simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary], by simp⟩

private theorem innerRedBlue_face0_blue_purple_support :
    boundaryBicoloredEdges sharedInteriorPairInnerRedBlueNeighbor blue purple
      (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace)) =
      ({sip01, sip23} : Finset sharedInteriorPairAnnulusGraph.edgeSet) := by
  apply Finset.ext
  intro e
  rw [mem_boundaryBicoloredEdges_iff]
  constructor
  · intro h
    rcases h with ⟨hface, hcolor⟩
    have hface' : e = sip01 ∨ e = sip12 ∨ e = sip23 ∨ e = sip30 := by
      simpa [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary] using hface
    rcases hface' with rfl | rfl | rfl | rfl
    · simp
    · rcases hcolor with hblue | hpurple
      · simp [sharedInteriorPairInnerRedBlueNeighbor_sip12, blue, red] at hblue
      · simp [sharedInteriorPairInnerRedBlueNeighbor_sip12, purple, red] at hpurple
    · simp
    · rcases hcolor with hblue | hpurple
      · simp [sharedInteriorPairInnerRedBlueNeighbor_sip30, blue, red] at hblue
      · simp [sharedInteriorPairInnerRedBlueNeighbor_sip30, purple, red] at hpurple
  · intro h
    rcases Finset.mem_insert.1 h with rfl | h
    · exact ⟨by simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary], by simp⟩
    rcases Finset.mem_singleton.1 h
    exact ⟨by simp [sharedInteriorPairAnnulusEmbedding, sharedInteriorPairFaceBoundary], by simp⟩

private theorem projected_explicit_face0_red_purple_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairTaitEdgeColoring red purple
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace))) =
      Pi.single sip01 blue := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      explicit_face0_red_purple_support, Pi.single, Function.update] <;>
    decide

private theorem projected_explicit_face0_blue_purple_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairTaitEdgeColoring blue purple
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace))) =
      Pi.single sip12 red := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      explicit_face0_blue_purple_support, Pi.single, Function.update] <;>
    decide

private theorem projected_innerRedBlue_face0_red_purple_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairInnerRedBlueNeighbor red purple
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace))) =
      Pi.single sip12 blue := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      innerRedBlue_face0_red_purple_support, Pi.single, Function.update] <;>
    decide

private theorem projected_innerRedBlue_face0_blue_purple_eq :
    sharedInteriorPairSelectedBoundaryProjection
      (polarizedFaceGenerator sharedInteriorPairInnerRedBlueNeighbor blue purple
        (sharedInteriorPairAnnulusEmbedding.faceBoundary (0 : SharedInteriorPairFace))) =
      Pi.single sip01 red := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sharedInteriorPairSelectedBoundaryProjection, polarizedFaceGenerator,
      innerRedBlue_face0_blue_purple_support, Pi.single, Function.update] <;>
    decide

private theorem single_sip01_blue_mem_radiusOneWitnessProjectedGeneratorSubspace :
    Pi.single sip01 blue ∈
      projectedColoringGeneratorSubspace sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairRadiusOneWitnessColorings := by
  rw [projectedColoringGeneratorSubspace_eq_span_projectedColoringGeneratorFamily]
  apply Submodule.subset_span
  exact (mem_projectedColoringGeneratorFamily_iff
    (emb := sharedInteriorPairAnnulusEmbedding)
    (colorings := sharedInteriorPairRadiusOneWitnessColorings)).2
    ⟨sharedInteriorPairTaitEdgeColoring, Or.inl rfl, (0 : SharedInteriorPairFace), red, purple,
      validColorPair_red_purple, projected_explicit_face0_red_purple_eq.symm⟩

private theorem single_sip12_red_mem_radiusOneWitnessProjectedGeneratorSubspace :
    Pi.single sip12 red ∈
      projectedColoringGeneratorSubspace sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairRadiusOneWitnessColorings := by
  rw [projectedColoringGeneratorSubspace_eq_span_projectedColoringGeneratorFamily]
  apply Submodule.subset_span
  exact (mem_projectedColoringGeneratorFamily_iff
    (emb := sharedInteriorPairAnnulusEmbedding)
    (colorings := sharedInteriorPairRadiusOneWitnessColorings)).2
    ⟨sharedInteriorPairTaitEdgeColoring, Or.inl rfl, (0 : SharedInteriorPairFace), blue, purple,
      validColorPair_blue_purple, projected_explicit_face0_blue_purple_eq.symm⟩

private theorem single_sip01_red_mem_radiusOneWitnessProjectedGeneratorSubspace :
    Pi.single sip01 red ∈
      projectedColoringGeneratorSubspace sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairRadiusOneWitnessColorings := by
  rw [projectedColoringGeneratorSubspace_eq_span_projectedColoringGeneratorFamily]
  apply Submodule.subset_span
  exact (mem_projectedColoringGeneratorFamily_iff
    (emb := sharedInteriorPairAnnulusEmbedding)
    (colorings := sharedInteriorPairRadiusOneWitnessColorings)).2
    ⟨sharedInteriorPairInnerRedBlueNeighbor, Or.inr rfl, (0 : SharedInteriorPairFace),
      blue, purple, validColorPair_blue_purple,
      projected_innerRedBlue_face0_blue_purple_eq.symm⟩

private theorem single_sip12_blue_mem_radiusOneWitnessProjectedGeneratorSubspace :
    Pi.single sip12 blue ∈
      projectedColoringGeneratorSubspace sharedInteriorPairAnnulusEmbedding
        sharedInteriorPairRadiusOneWitnessColorings := by
  rw [projectedColoringGeneratorSubspace_eq_span_projectedColoringGeneratorFamily]
  apply Submodule.subset_span
  exact (mem_projectedColoringGeneratorFamily_iff
    (emb := sharedInteriorPairAnnulusEmbedding)
    (colorings := sharedInteriorPairRadiusOneWitnessColorings)).2
    ⟨sharedInteriorPairInnerRedBlueNeighbor, Or.inr rfl, (0 : SharedInteriorPairFace),
      red, purple, validColorPair_red_purple,
      projected_innerRedBlue_face0_red_purple_eq.symm⟩

private theorem eq_zero_of_mem_planarBoundaryZeroSubmodule_of_zero_on_sip01_of_zero_on_sip12
    {z : sharedInteriorPairAnnulusGraph.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule sharedInteriorPairAnnulusEmbedding)
    (hsip01 : z sip01 = 0) (hsip12 : z sip12 = 0) :
    z = 0 := by
  funext e
  rcases sharedInteriorPairAnnulus_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsip01
  · exact hsip12
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz sip23 (by simp)
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz sip30 (by simp)
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz sip24 (by simp)
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz sip40 (by simp)
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz sip56 (by simp)
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz sip67 (by simp)
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz sip75 (by simp)

/-- Kernel-checked radius-1 detector on the shared benchmark, sharpened beyond the finite lab:
two explicit colorings already suffice, namely the benchmark coloring and the single inner
red/blue Kempe neighbor. -/
theorem sharedInteriorPairAnnulusEmbedding_boundaryZeroProjectedColoringGeneratorDetector_for_radiusOneWitnessColorings :
    BoundaryZeroProjectedColoringGeneratorDetector sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairRadiusOneWitnessColorings := by
  refine BoundaryZeroProjectedColoringGeneratorDetector.of_singleCoordinateWitnesses
    ({sip01, sip12} : Finset sharedInteriorPairAnnulusGraph.edgeSet)
    ?_ ?_
  · intro z hzBoundary hzero
    exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_zero_on_sip01_of_zero_on_sip12
      hzBoundary (hzero sip01 (by simp)) (hzero sip12 (by simp))
  · intro e he d hd
    rcases Finset.mem_insert.1 he with rfl | he
    · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero d hd with hred | hblue | hpurple
      · refine ⟨red, single_sip01_red_mem_radiusOneWitnessProjectedGeneratorSubspace, ?_⟩
        simp [hred, colorDot, red]
      · refine ⟨blue, single_sip01_blue_mem_radiusOneWitnessProjectedGeneratorSubspace, ?_⟩
        simp [hblue, colorDot, blue]
      · refine ⟨red, single_sip01_red_mem_radiusOneWitnessProjectedGeneratorSubspace, ?_⟩
        simp [hpurple, colorDot, red, purple]
    rcases Finset.mem_singleton.1 he
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero d hd with hred | hblue | hpurple
    · refine ⟨red, single_sip12_red_mem_radiusOneWitnessProjectedGeneratorSubspace, ?_⟩
      simp [hred, colorDot, red]
    · refine ⟨blue, single_sip12_blue_mem_radiusOneWitnessProjectedGeneratorSubspace, ?_⟩
      simp [hblue, colorDot, blue]
    · refine ⟨red, single_sip12_red_mem_radiusOneWitnessProjectedGeneratorSubspace, ?_⟩
      simp [hpurple, colorDot, red, purple]

/-- The preserved finite lab's seven-color shared radius-1 neighborhood therefore kernel-checks
in Lean as a projected-generator detector. -/
theorem sharedInteriorPairAnnulusEmbedding_boundaryZeroProjectedColoringGeneratorDetector_for_radiusOneColorings :
    BoundaryZeroProjectedColoringGeneratorDetector sharedInteriorPairAnnulusEmbedding
      sharedInteriorPairRadiusOneColorings :=
  BoundaryZeroProjectedColoringGeneratorDetector.mono
    sharedInteriorPairAnnulusEmbedding_boundaryZeroProjectedColoringGeneratorDetector_for_radiusOneWitnessColorings
    sharedInteriorPairRadiusOneWitnessColorings_subset_radiusOne

end Theorem49SharedInteriorPairRadiusOneDetectorRegression

end Mettapedia.GraphTheory.FourColor
