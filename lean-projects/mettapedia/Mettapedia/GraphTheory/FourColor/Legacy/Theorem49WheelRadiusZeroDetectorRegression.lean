import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorCoordinateDetector
import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49PlanarBoundaryAnnulusWheelWitnessRegression
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

namespace Theorem49WheelRadiusZeroDetectorRegression

private noncomputable instance : Fintype wheelWithInnerTriangleGraph.edgeSet :=
  Theorem49PlanarBoundaryAnnulusWheelWitnessRegression.wheelWithInnerTriangleGraph_edgeSet_fintype

attribute [simp] wit12_mem_selectedBoundarySupport
attribute [simp] wit23_mem_selectedBoundarySupport
attribute [simp] wit31_mem_selectedBoundarySupport
attribute [simp] wit45_mem_selectedBoundarySupport
attribute [simp] wit56_mem_selectedBoundarySupport
attribute [simp] wit64_mem_selectedBoundarySupport
attribute [simp] wit01_not_mem_selectedBoundarySupport
attribute [simp] wit02_not_mem_selectedBoundarySupport
attribute [simp] wit03_not_mem_selectedBoundarySupport

private theorem validColorPair_red_blue : ValidColorPair red blue :=
  ⟨red_ne_zero, blue_ne_zero, red_ne_blue⟩

private theorem validColorPair_red_purple : ValidColorPair red purple :=
  ⟨red_ne_zero, purple_ne_zero, red_ne_purple⟩

private theorem validColorPair_blue_purple : ValidColorPair blue purple :=
  ⟨blue_ne_zero, purple_ne_zero, blue_ne_purple⟩

private def wheelRadiusZeroColorings :
    Set (wheelWithInnerTriangleGraph.EdgeColoring Color) :=
  {wheelWithInnerTriangleTaitEdgeColoring}

private def wheelSelectedBoundaryProjection :
    (wheelWithInnerTriangleGraph.edgeSet → Color) →ₗ[F2]
      (wheelWithInnerTriangleGraph.edgeSet → Color) :=
  boundaryZeroProjection
    (selectedBoundarySupport
      wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleEmbedding.faces
      wheelWithInnerTriangleEmbedding.faces)

private theorem face0_red_purple_support :
    boundaryBicoloredEdges wheelWithInnerTriangleTaitEdgeColoring red purple
      (wheelWithInnerTriangleEmbedding.faceBoundary (0 : WheelWithInnerTriangleFace)) =
      ({wit01, wit12} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
  decide

private theorem face2_red_blue_support :
    boundaryBicoloredEdges wheelWithInnerTriangleTaitEdgeColoring red blue
      (wheelWithInnerTriangleEmbedding.faceBoundary (2 : WheelWithInnerTriangleFace)) =
      ({wit01, wit31} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
  decide

private theorem face0_blue_purple_support :
    boundaryBicoloredEdges wheelWithInnerTriangleTaitEdgeColoring blue purple
      (wheelWithInnerTriangleEmbedding.faceBoundary (0 : WheelWithInnerTriangleFace)) =
      ({wit02, wit12} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
  decide

private theorem face1_red_blue_support :
    boundaryBicoloredEdges wheelWithInnerTriangleTaitEdgeColoring red blue
      (wheelWithInnerTriangleEmbedding.faceBoundary (1 : WheelWithInnerTriangleFace)) =
      ({wit02, wit23} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
  decide

private theorem face1_red_purple_support :
    boundaryBicoloredEdges wheelWithInnerTriangleTaitEdgeColoring red purple
      (wheelWithInnerTriangleEmbedding.faceBoundary (1 : WheelWithInnerTriangleFace)) =
      ({wit03, wit23} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
  decide

private theorem face2_blue_purple_support :
    boundaryBicoloredEdges wheelWithInnerTriangleTaitEdgeColoring blue purple
      (wheelWithInnerTriangleEmbedding.faceBoundary (2 : WheelWithInnerTriangleFace)) =
      ({wit03, wit31} : Finset wheelWithInnerTriangleGraph.edgeSet) := by
  decide

private theorem projected_face0_red_purple_eq :
    wheelSelectedBoundaryProjection
      (polarizedFaceGenerator wheelWithInnerTriangleTaitEdgeColoring red purple
        (wheelWithInnerTriangleEmbedding.faceBoundary (0 : WheelWithInnerTriangleFace))) =
      Pi.single wit01 blue := by
  funext e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelSelectedBoundaryProjection, polarizedFaceGenerator, face0_red_purple_support,
      Pi.single, Function.update] <;>
    decide

private theorem projected_face2_red_blue_eq :
    wheelSelectedBoundaryProjection
      (polarizedFaceGenerator wheelWithInnerTriangleTaitEdgeColoring red blue
        (wheelWithInnerTriangleEmbedding.faceBoundary (2 : WheelWithInnerTriangleFace))) =
      Pi.single wit01 purple := by
  funext e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelSelectedBoundaryProjection, polarizedFaceGenerator, face2_red_blue_support,
      Pi.single, Function.update] <;>
    decide

private theorem projected_face0_blue_purple_eq :
    wheelSelectedBoundaryProjection
      (polarizedFaceGenerator wheelWithInnerTriangleTaitEdgeColoring blue purple
        (wheelWithInnerTriangleEmbedding.faceBoundary (0 : WheelWithInnerTriangleFace))) =
      Pi.single wit02 red := by
  funext e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelSelectedBoundaryProjection, polarizedFaceGenerator, face0_blue_purple_support,
      Pi.single, Function.update] <;>
    decide

private theorem projected_face1_red_blue_eq :
    wheelSelectedBoundaryProjection
      (polarizedFaceGenerator wheelWithInnerTriangleTaitEdgeColoring red blue
        (wheelWithInnerTriangleEmbedding.faceBoundary (1 : WheelWithInnerTriangleFace))) =
      Pi.single wit02 purple := by
  funext e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelSelectedBoundaryProjection, polarizedFaceGenerator, face1_red_blue_support,
      Pi.single, Function.update] <;>
    decide

private theorem projected_face1_red_purple_eq :
    wheelSelectedBoundaryProjection
      (polarizedFaceGenerator wheelWithInnerTriangleTaitEdgeColoring red purple
        (wheelWithInnerTriangleEmbedding.faceBoundary (1 : WheelWithInnerTriangleFace))) =
      Pi.single wit03 blue := by
  funext e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelSelectedBoundaryProjection, polarizedFaceGenerator, face1_red_purple_support,
      Pi.single, Function.update] <;>
    decide

private theorem projected_face2_blue_purple_eq :
    wheelSelectedBoundaryProjection
      (polarizedFaceGenerator wheelWithInnerTriangleTaitEdgeColoring blue purple
        (wheelWithInnerTriangleEmbedding.faceBoundary (2 : WheelWithInnerTriangleFace))) =
      Pi.single wit03 red := by
  funext e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wheelSelectedBoundaryProjection, polarizedFaceGenerator, face2_blue_purple_support,
      Pi.single, Function.update] <;>
    decide

private theorem single_wit01_blue_mem_radiusZeroProjectedGeneratorSubspace :
    Pi.single wit01 blue ∈
      projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding wheelRadiusZeroColorings := by
  rw [projectedColoringGeneratorSubspace_eq_span_projectedColoringGeneratorFamily]
  apply Submodule.subset_span
  exact (mem_projectedColoringGeneratorFamily_iff
    (emb := wheelWithInnerTriangleEmbedding)
    (colorings := wheelRadiusZeroColorings)).2
    ⟨wheelWithInnerTriangleTaitEdgeColoring, by simp [wheelRadiusZeroColorings],
      (0 : WheelWithInnerTriangleFace), red, purple, validColorPair_red_purple,
      projected_face0_red_purple_eq.symm⟩

private theorem single_wit01_purple_mem_radiusZeroProjectedGeneratorSubspace :
    Pi.single wit01 purple ∈
      projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding wheelRadiusZeroColorings := by
  rw [projectedColoringGeneratorSubspace_eq_span_projectedColoringGeneratorFamily]
  apply Submodule.subset_span
  exact (mem_projectedColoringGeneratorFamily_iff
    (emb := wheelWithInnerTriangleEmbedding)
    (colorings := wheelRadiusZeroColorings)).2
    ⟨wheelWithInnerTriangleTaitEdgeColoring, by simp [wheelRadiusZeroColorings],
      (2 : WheelWithInnerTriangleFace), red, blue, validColorPair_red_blue,
      projected_face2_red_blue_eq.symm⟩

private theorem single_wit02_red_mem_radiusZeroProjectedGeneratorSubspace :
    Pi.single wit02 red ∈
      projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding wheelRadiusZeroColorings := by
  rw [projectedColoringGeneratorSubspace_eq_span_projectedColoringGeneratorFamily]
  apply Submodule.subset_span
  exact (mem_projectedColoringGeneratorFamily_iff
    (emb := wheelWithInnerTriangleEmbedding)
    (colorings := wheelRadiusZeroColorings)).2
    ⟨wheelWithInnerTriangleTaitEdgeColoring, by simp [wheelRadiusZeroColorings],
      (0 : WheelWithInnerTriangleFace), blue, purple, validColorPair_blue_purple,
      projected_face0_blue_purple_eq.symm⟩

private theorem single_wit02_purple_mem_radiusZeroProjectedGeneratorSubspace :
    Pi.single wit02 purple ∈
      projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding wheelRadiusZeroColorings := by
  rw [projectedColoringGeneratorSubspace_eq_span_projectedColoringGeneratorFamily]
  apply Submodule.subset_span
  exact (mem_projectedColoringGeneratorFamily_iff
    (emb := wheelWithInnerTriangleEmbedding)
    (colorings := wheelRadiusZeroColorings)).2
    ⟨wheelWithInnerTriangleTaitEdgeColoring, by simp [wheelRadiusZeroColorings],
      (1 : WheelWithInnerTriangleFace), red, blue, validColorPair_red_blue,
      projected_face1_red_blue_eq.symm⟩

private theorem single_wit03_blue_mem_radiusZeroProjectedGeneratorSubspace :
    Pi.single wit03 blue ∈
      projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding wheelRadiusZeroColorings := by
  rw [projectedColoringGeneratorSubspace_eq_span_projectedColoringGeneratorFamily]
  apply Submodule.subset_span
  exact (mem_projectedColoringGeneratorFamily_iff
    (emb := wheelWithInnerTriangleEmbedding)
    (colorings := wheelRadiusZeroColorings)).2
    ⟨wheelWithInnerTriangleTaitEdgeColoring, by simp [wheelRadiusZeroColorings],
      (1 : WheelWithInnerTriangleFace), red, purple, validColorPair_red_purple,
      projected_face1_red_purple_eq.symm⟩

private theorem single_wit03_red_mem_radiusZeroProjectedGeneratorSubspace :
    Pi.single wit03 red ∈
      projectedColoringGeneratorSubspace wheelWithInnerTriangleEmbedding wheelRadiusZeroColorings := by
  rw [projectedColoringGeneratorSubspace_eq_span_projectedColoringGeneratorFamily]
  apply Submodule.subset_span
  exact (mem_projectedColoringGeneratorFamily_iff
    (emb := wheelWithInnerTriangleEmbedding)
    (colorings := wheelRadiusZeroColorings)).2
    ⟨wheelWithInnerTriangleTaitEdgeColoring, by simp [wheelRadiusZeroColorings],
      (2 : WheelWithInnerTriangleFace), blue, purple, validColorPair_blue_purple,
      projected_face2_blue_purple_eq.symm⟩

private theorem eq_zero_of_mem_planarBoundaryZeroSubmodule_of_zero_on_spokes
    {z : wheelWithInnerTriangleGraph.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule wheelWithInnerTriangleEmbedding)
    (hwit01 : z wit01 = 0) (hwit02 : z wit02 = 0) (hwit03 : z wit03 = 0) :
    z = 0 := by
  funext e
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hwit01
  · exact hwit02
  · exact hwit03
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz wit12 (by simp)
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz wit23 (by simp)
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz wit31 (by simp)
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz wit45 (by simp)
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz wit56 (by simp)
  · exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz wit64 (by simp)

/-- Kernel-checked exact radius-0 detector on the wheel benchmark: the explicit benchmark
coloring alone already detects every nonzero selected-boundary-zero chain. -/
theorem wheelWithInnerTriangleEmbedding_boundaryZeroProjectedColoringGeneratorDetector_for_radiusZeroColorings :
    BoundaryZeroProjectedColoringGeneratorDetector wheelWithInnerTriangleEmbedding
      wheelRadiusZeroColorings := by
  refine BoundaryZeroProjectedColoringGeneratorDetector.of_singleCoordinateWitnesses
    ({wit01, wit02, wit03} : Finset wheelWithInnerTriangleGraph.edgeSet)
    ?_ ?_
  · intro z hzBoundary hzero
    exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_zero_on_spokes hzBoundary
      (hzero wit01 (by simp)) (hzero wit02 (by simp)) (hzero wit03 (by simp))
  · intro e he d hd
    rcases Finset.mem_insert.1 he with rfl | he
    · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero d hd with hred | hblue | hpurple
      · refine ⟨purple, single_wit01_purple_mem_radiusZeroProjectedGeneratorSubspace, ?_⟩
        simp [hred, colorDot, red, purple]
      · refine ⟨blue, single_wit01_blue_mem_radiusZeroProjectedGeneratorSubspace, ?_⟩
        simp [hblue, colorDot, blue]
      · refine ⟨blue, single_wit01_blue_mem_radiusZeroProjectedGeneratorSubspace, ?_⟩
        simp [hpurple, colorDot, blue, purple]
    rcases Finset.mem_insert.1 he with rfl | he
    · rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero d hd with hred | hblue | hpurple
      · refine ⟨red, single_wit02_red_mem_radiusZeroProjectedGeneratorSubspace, ?_⟩
        simp [hred, colorDot, red]
      · refine ⟨purple, single_wit02_purple_mem_radiusZeroProjectedGeneratorSubspace, ?_⟩
        simp [hblue, colorDot, blue, purple]
      · refine ⟨red, single_wit02_red_mem_radiusZeroProjectedGeneratorSubspace, ?_⟩
        simp [hpurple, colorDot, red, purple]
    rcases Finset.mem_singleton.1 he
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero d hd with hred | hblue | hpurple
    · refine ⟨red, single_wit03_red_mem_radiusZeroProjectedGeneratorSubspace, ?_⟩
      simp [hred, colorDot, red]
    · refine ⟨blue, single_wit03_blue_mem_radiusZeroProjectedGeneratorSubspace, ?_⟩
      simp [hblue, colorDot, blue]
    · refine ⟨red, single_wit03_red_mem_radiusZeroProjectedGeneratorSubspace, ?_⟩
      simp [hpurple, colorDot, red, purple]

end Theorem49WheelRadiusZeroDetectorRegression

end Mettapedia.GraphTheory.FourColor
