import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorFamily
import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryProjectionDetector

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- An explicit projected-generator detector on any coloring family contained in the base
edge-Kempe closure already upgrades to the full closure-wide detector.  This is the direct bridge
from small finite certificates to the existing theorem-4.9 endpoint route. -/
theorem BoundaryZeroProjectedGeneratorDetector.of_coloringFamily
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {colorings : Set (G.EdgeColoring Color)}
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (hdet : BoundaryZeroProjectedColoringGeneratorDetector emb colorings) :
    BoundaryZeroProjectedGeneratorDetector emb C₀ := by
  have hdetClosure :
      BoundaryZeroProjectedColoringGeneratorDetector emb (G.EdgeKempeClosure C₀) :=
    BoundaryZeroProjectedColoringGeneratorDetector.mono hdet hsubset
  intro z hzBoundary hzNonzero
  rcases hdetClosure hzBoundary hzNonzero with ⟨p, hp, hpair⟩
  have hproj :
      projectedKempeClosureGeneratorSubspace emb C₀ =
        projectedColoringGeneratorSubspace emb (G.EdgeKempeClosure C₀) :=
    projectedKempeClosureGeneratorSubspace_eq_projectedColoringGeneratorSubspace_edgeKempeClosure
      emb C₀
  exact ⟨p, by simpa [hproj] using hp, hpair⟩

/-- Route theorem for explicit finite certificates: once some coloring subfamily inside the
chosen edge-Kempe closure detects every nonzero selected-boundary-zero chain, the full current
theorem-4.9 synthesis package follows for the base coloring. -/
theorem theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedColoringGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (hdet : BoundaryZeroProjectedColoringGeneratorDetector emb colorings) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedGeneratorDetector emb C₀
    (BoundaryZeroProjectedGeneratorDetector.of_coloringFamily hsubset hdet)

end Mettapedia.GraphTheory.FourColor
