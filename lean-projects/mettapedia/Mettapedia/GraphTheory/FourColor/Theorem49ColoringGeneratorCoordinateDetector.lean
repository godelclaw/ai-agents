import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorFamilyRoute

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- An explicit projected coloring family detects every nonzero selected-boundary-zero chain once
a finite set of controlling coordinates has two ingredients:

1. vanishing on those coordinates forces vanishing of the whole chain; and
2. every nonzero value on each controlling coordinate is separated by some projected generator
   equal to a single-coordinate chain there.

This is the direct Lean interface for the current finite-lab certificates on the wheel/shared
benchmarks, and for future explicit finite `F₂` detector outputs of the same shape. -/
theorem BoundaryZeroProjectedColoringGeneratorDetector.of_singleCoordinateWitnesses
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ c : Color,
          Pi.single e c ∈ projectedColoringGeneratorSubspace emb colorings ∧
            colorDot c d ≠ 0) :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings := by
  intro z hzBoundary hzNonzero
  classical
  have hcoord : ∃ e ∈ controlEdges, z e ≠ 0 := by
    by_contra hnone
    apply hzNonzero
    apply hcontrol hzBoundary
    intro e he
    by_contra hze
    exact hnone ⟨e, he, hze⟩
  rcases hcoord with ⟨e, he, hze⟩
  rcases hwitness e he (z e) hze with ⟨c, hcmem, hcdot⟩
  refine ⟨Pi.single e c, hcmem, ?_⟩
  rw [chainDotBilinForm_single_left]
  exact hcdot

/-- Route form of the same explicit coordinate certificate: once an explicit coloring family
inside the chosen edge-Kempe closure has enough single-coordinate witnesses on a controlling edge
set, the full theorem-4.9 synthesis package follows for the base coloring. -/
theorem theorem49BoundaryRootSynthesis_of_singleCoordinateWitnesses
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitness :
      ∀ e ∈ controlEdges, ∀ d : Color, d ≠ 0 →
        ∃ c : Color,
          Pi.single e c ∈ projectedColoringGeneratorSubspace emb colorings ∧
            colorDot c d ≠ 0) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedColoringGeneratorDetector
    emb C₀ colorings hsubset
    (BoundaryZeroProjectedColoringGeneratorDetector.of_singleCoordinateWitnesses
      controlEdges hcontrol hwitness)

end Mettapedia.GraphTheory.FourColor
