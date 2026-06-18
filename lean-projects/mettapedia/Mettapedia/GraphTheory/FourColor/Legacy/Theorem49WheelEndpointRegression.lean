import Mettapedia.GraphTheory.FourColor.Legacy.Theorem49PlanarBoundaryAnnulusWheelWitnessRegression
import Mettapedia.GraphTheory.FourColor.Theorem49Synthesis
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open Theorem49PlanarBoundaryAnnulusWheelWitnessRegression

namespace Theorem49WheelEndpointRegression

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

private theorem zero_on_wit12 {z : wheelWithInnerTriangleGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces,
        z e = 0) :
    z wit12 = 0 :=
  hzeroBoundary wit12 wit12_mem_selectedBoundarySupport

private theorem zero_on_wit23 {z : wheelWithInnerTriangleGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces,
        z e = 0) :
    z wit23 = 0 :=
  hzeroBoundary wit23 wit23_mem_selectedBoundarySupport

private theorem zero_on_wit31 {z : wheelWithInnerTriangleGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces,
        z e = 0) :
    z wit31 = 0 :=
  hzeroBoundary wit31 wit31_mem_selectedBoundarySupport

private theorem zero_on_wit45 {z : wheelWithInnerTriangleGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces,
        z e = 0) :
    z wit45 = 0 :=
  hzeroBoundary wit45 wit45_mem_selectedBoundarySupport

private theorem zero_on_wit56 {z : wheelWithInnerTriangleGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces,
        z e = 0) :
    z wit56 = 0 :=
  hzeroBoundary wit56 wit56_mem_selectedBoundarySupport

private theorem zero_on_wit64 {z : wheelWithInnerTriangleGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces,
        z e = 0) :
    z wit64 = 0 :=
  hzeroBoundary wit64 wit64_mem_selectedBoundarySupport

private theorem zero_on_wit01_of_boundaryZero_and_annihilator
    {z : wheelWithInnerTriangleGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces,
        z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleTaitEdgeColoring z) :
    z wit01 = 0 := by
  apply eq_zero_of_colorDot_eq_zero_for_all_nonzero_ne (z := z wit01) (d := red)
  · exact red_ne_zero
  · intro γ hγ0 hγne
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero γ hγ0 with rfl | rfl | rfl
    · exact False.elim (hγne rfl)
    · have horth :=
        localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
          (faceBoundary := wheelWithInnerTriangleEmbedding.faceBoundary)
          (hC := wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self
            wheelWithInnerTriangleTaitEdgeColoring)
          hgen
          (f := (0 : WheelWithInnerTriangleFace))
          (e := wit01)
          (wheelWithInnerTriangleTaitEdgeColoring_isTait wit01)
          blue blue_ne_zero (by decide)
      have hchain :
          chainDot ({wit01, wit12} : Finset wheelWithInnerTriangleGraph.edgeSet) z
            (indicatorChain blue ({wit01, wit12} : Finset wheelWithInnerTriangleGraph.edgeSet)) =
            0 := by
        simpa [wheelWithInnerTriangleTaitEdgeColoring, wheelWithInnerTriangleEdgeColor_wit01,
          face0_red_purple_support,
          polarizedFaceGenerator_eq_indicatorChain_of_add_pair] using horth
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero (e := wit01) blue (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ wit01 := (Finset.mem_erase.1 he).1
        have hmem : e = wit01 ∨ e = wit12 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl
        · exact False.elim (hne rfl)
        · exact zero_on_wit12 hzeroBoundary
    · have horth :=
        localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
          (faceBoundary := wheelWithInnerTriangleEmbedding.faceBoundary)
          (hC := wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self
            wheelWithInnerTriangleTaitEdgeColoring)
          hgen
          (f := (2 : WheelWithInnerTriangleFace))
          (e := wit01)
          (wheelWithInnerTriangleTaitEdgeColoring_isTait wit01)
          purple purple_ne_zero (by decide)
      have hchain :
          chainDot ({wit01, wit31} : Finset wheelWithInnerTriangleGraph.edgeSet) z
            (indicatorChain purple ({wit01, wit31} : Finset wheelWithInnerTriangleGraph.edgeSet))
              = 0 := by
        simpa [wheelWithInnerTriangleTaitEdgeColoring, wheelWithInnerTriangleEdgeColor_wit01,
          face2_red_blue_support,
          polarizedFaceGenerator_eq_indicatorChain_of_add_pair] using horth
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero (e := wit01) purple (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ wit01 := (Finset.mem_erase.1 he).1
        have hmem : e = wit01 ∨ e = wit31 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl
        · exact False.elim (hne rfl)
        · exact zero_on_wit31 hzeroBoundary

private theorem zero_on_wit02_of_boundaryZero_and_annihilator
    {z : wheelWithInnerTriangleGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces,
        z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleTaitEdgeColoring z) :
    z wit02 = 0 := by
  apply eq_zero_of_colorDot_eq_zero_for_all_nonzero_ne (z := z wit02) (d := blue)
  · exact blue_ne_zero
  · intro γ hγ0 hγne
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero γ hγ0 with rfl | rfl | rfl
    · have horth :=
        localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
          (faceBoundary := wheelWithInnerTriangleEmbedding.faceBoundary)
          (hC := wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self
            wheelWithInnerTriangleTaitEdgeColoring)
          hgen
          (f := (0 : WheelWithInnerTriangleFace))
          (e := wit02)
          (wheelWithInnerTriangleTaitEdgeColoring_isTait wit02)
          red red_ne_zero (by decide)
      have hchain :
          chainDot ({wit02, wit12} : Finset wheelWithInnerTriangleGraph.edgeSet) z
            (indicatorChain red ({wit02, wit12} : Finset wheelWithInnerTriangleGraph.edgeSet)) =
            0 := by
        simpa [wheelWithInnerTriangleTaitEdgeColoring, wheelWithInnerTriangleEdgeColor_wit02,
          face0_blue_purple_support,
          polarizedFaceGenerator_eq_indicatorChain_of_add_pair] using horth
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero (e := wit02) red (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ wit02 := (Finset.mem_erase.1 he).1
        have hmem : e = wit02 ∨ e = wit12 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl
        · exact False.elim (hne rfl)
        · exact zero_on_wit12 hzeroBoundary
    · exact False.elim (hγne rfl)
    · have horth :=
        localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
          (faceBoundary := wheelWithInnerTriangleEmbedding.faceBoundary)
          (hC := wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self
            wheelWithInnerTriangleTaitEdgeColoring)
          hgen
          (f := (1 : WheelWithInnerTriangleFace))
          (e := wit02)
          (wheelWithInnerTriangleTaitEdgeColoring_isTait wit02)
          purple purple_ne_zero (by decide)
      have hchain :
          chainDot ({wit02, wit23} : Finset wheelWithInnerTriangleGraph.edgeSet) z
            (indicatorChain purple ({wit02, wit23} : Finset wheelWithInnerTriangleGraph.edgeSet))
              = 0 := by
        simpa [wheelWithInnerTriangleTaitEdgeColoring, wheelWithInnerTriangleEdgeColor_wit02,
          face1_red_blue_support,
          polarizedFaceGenerator_eq_indicatorChain_of_add_pair] using horth
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero (e := wit02) purple (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ wit02 := (Finset.mem_erase.1 he).1
        have hmem : e = wit02 ∨ e = wit23 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl
        · exact False.elim (hne rfl)
        · exact zero_on_wit23 hzeroBoundary

private theorem zero_on_wit03_of_boundaryZero_and_annihilator
    {z : wheelWithInnerTriangleGraph.edgeSet → Color}
    (hzeroBoundary :
      ∀ e ∈ selectedBoundarySupport wheelWithInnerTriangleEmbedding.faceBoundary
          wheelWithInnerTriangleEmbedding.faces wheelWithInnerTriangleEmbedding.faces,
        z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily wheelWithInnerTriangleEmbedding.faceBoundary
      wheelWithInnerTriangleTaitEdgeColoring z) :
    z wit03 = 0 := by
  apply eq_zero_of_colorDot_eq_zero_for_all_nonzero_ne (z := z wit03) (d := purple)
  · exact purple_ne_zero
  · intro γ hγ0 hγne
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero γ hγ0 with rfl | rfl | rfl
    · have horth :=
        localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
          (faceBoundary := wheelWithInnerTriangleEmbedding.faceBoundary)
          (hC := wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self
            wheelWithInnerTriangleTaitEdgeColoring)
          hgen
          (f := (2 : WheelWithInnerTriangleFace))
          (e := wit03)
          (wheelWithInnerTriangleTaitEdgeColoring_isTait wit03)
          red red_ne_zero (by decide)
      have hchain :
          chainDot ({wit03, wit31} : Finset wheelWithInnerTriangleGraph.edgeSet) z
            (indicatorChain red ({wit03, wit31} : Finset wheelWithInnerTriangleGraph.edgeSet)) =
            0 := by
        simpa [wheelWithInnerTriangleTaitEdgeColoring, wheelWithInnerTriangleEdgeColor_wit03,
          face2_blue_purple_support,
          polarizedFaceGenerator_eq_indicatorChain_of_add_pair] using horth
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero (e := wit03) red (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ wit03 := (Finset.mem_erase.1 he).1
        have hmem : e = wit03 ∨ e = wit31 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl
        · exact False.elim (hne rfl)
        · exact zero_on_wit31 hzeroBoundary
    · have horth :=
        localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
          (faceBoundary := wheelWithInnerTriangleEmbedding.faceBoundary)
          (hC := wheelWithInnerTriangleGraph.mem_edgeKempeClosure_self
            wheelWithInnerTriangleTaitEdgeColoring)
          hgen
          (f := (1 : WheelWithInnerTriangleFace))
          (e := wit03)
          (wheelWithInnerTriangleTaitEdgeColoring_isTait wit03)
          blue blue_ne_zero (by decide)
      have hchain :
          chainDot ({wit03, wit23} : Finset wheelWithInnerTriangleGraph.edgeSet) z
            (indicatorChain blue ({wit03, wit23} : Finset wheelWithInnerTriangleGraph.edgeSet)) =
            0 := by
        simpa [wheelWithInnerTriangleTaitEdgeColoring, wheelWithInnerTriangleEdgeColor_wit03,
          face1_red_purple_support,
          polarizedFaceGenerator_eq_indicatorChain_of_add_pair] using horth
      rw [chainDot_indicatorChain_eq_colorDot_of_erase_zero (e := wit03) blue (by simp)] at hchain
      · exact hchain
      · intro e he
        have hne : e ≠ wit03 := (Finset.mem_erase.1 he).1
        have hmem : e = wit03 ∨ e = wit23 := by
          simpa using (Finset.mem_erase.1 he).2
        rcases hmem with rfl | rfl
        · exact False.elim (hne rfl)
        · exact zero_on_wit23 hzeroBoundary
    · exact False.elim (hγne rfl)

/-- The wheel benchmark already satisfies the current endpoint directly for the explicit Tait
coloring: every selected-boundary-zero chain annihilating the radius-0 projected generators is
forced to vanish on all nine edges. -/
theorem wheelWithInnerTriangleEmbedding_boundaryZeroAnnihilatorTrivial_for_explicitTaitColoring :
    BoundaryZeroAnnihilatorTrivialForEmbedding wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleTaitEdgeColoring := by
  intro z hzeroBoundary hgen e
  have hwit01 : z wit01 = 0 :=
    zero_on_wit01_of_boundaryZero_and_annihilator hzeroBoundary hgen
  have hwit02 : z wit02 = 0 :=
    zero_on_wit02_of_boundaryZero_and_annihilator hzeroBoundary hgen
  have hwit03 : z wit03 = 0 :=
    zero_on_wit03_of_boundaryZero_and_annihilator hzeroBoundary hgen
  have hwit12 : z wit12 = 0 := zero_on_wit12 hzeroBoundary
  have hwit23 : z wit23 = 0 := zero_on_wit23 hzeroBoundary
  have hwit31 : z wit31 = 0 := zero_on_wit31 hzeroBoundary
  have hwit45 : z wit45 = 0 := zero_on_wit45 hzeroBoundary
  have hwit56 : z wit56 = 0 := zero_on_wit56 hzeroBoundary
  have hwit64 : z wit64 = 0 := zero_on_wit64 hzeroBoundary
  rcases wheelWithInnerTriangle_edge_eq e with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

/-- Kernel-checked endpoint on the honest wheel embedding for the explicit benchmark coloring.
This confirms the lab result that the current wheel pathology kills the four geometric routes but
does not kill the theorem-4.9 synthesis endpoint itself. -/
theorem wheelWithInnerTriangleEmbedding_theorem49BoundaryRootSynthesis_for_explicitTaitColoring
    [FiniteDimensional F2 (wheelWithInnerTriangleGraph.edgeSet → Color)] :
    Theorem49BoundaryRootSynthesis wheelWithInnerTriangleEmbedding
      wheelWithInnerTriangleTaitEdgeColoring := by
  exact theorem49BoundaryRootSynthesis_of_boundaryZeroAnnihilatorTrivial
    wheelWithInnerTriangleTaitEdgeColoring
    wheelWithInnerTriangleEmbedding_boundaryZeroAnnihilatorTrivial_for_explicitTaitColoring

end Theorem49WheelEndpointRegression

end Mettapedia.GraphTheory.FourColor
