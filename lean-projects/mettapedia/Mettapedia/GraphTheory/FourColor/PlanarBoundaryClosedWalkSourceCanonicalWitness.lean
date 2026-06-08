import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceRoute
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceImpossibility

/-!
# Source-side criterion for canonical witness choice

This file keeps the canonical-witness question at the honest closed-walk source
layer.  The route file already constructs a canonical witness choice from the
source plus the facewise at-most-one interior-edge condition, while the positive
source obstruction file proves the reverse implication for any canonical
witness choice.  Combining the two gives the exact source-side obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- On an honest closed-walk annulus source, source-boundary canonical witness
choice is equivalent to the facewise at-most-one interior-edge condition. -/
theorem nonempty_planarBoundaryCanonicalWitnessChoice_iff_facewiseAtMostOneInteriorEdge_of_closedWalkAnnulusBoundarySource
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    Nonempty
        (PlanarBoundaryCanonicalWitnessChoice
          source.toPlanarBoundaryAnnulusBoundaryData) ↔
      ∀ f : AmbientFace emb.faces,
        ((emb.faceBoundary f.1).filter
          (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1 := by
  constructor
  · intro hchoice
    exact facewiseAtMostOneInteriorEdge_of_planarBoundaryCanonicalWitnessChoice hchoice
  · intro hAtMost
    exact
      exists_planarBoundaryCanonicalWitnessChoice_of_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
        source hAtMost

/-- Graph-level source criterion: exhibiting an honest closed-walk source with a
canonical witness choice is exactly exhibiting such a source with the facewise
at-most-one interior-edge condition. -/
theorem exists_closedWalkAnnulusBoundarySource_and_planarBoundaryCanonicalWitnessChoice_iff_exists_closedWalkAnnulusBoundarySource_and_facewiseAtMostOneInteriorEdge
    {G : SimpleGraph V} :
    (∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty
          (PlanarBoundaryCanonicalWitnessChoice
            source.toPlanarBoundaryAnnulusBoundaryData)) ↔
      (∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
              (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) := by
  constructor
  · rintro ⟨emb, source, hchoice⟩
    exact
      ⟨emb, source,
        (nonempty_planarBoundaryCanonicalWitnessChoice_iff_facewiseAtMostOneInteriorEdge_of_closedWalkAnnulusBoundarySource
          source).1 hchoice⟩
  · rintro ⟨emb, source, hAtMost⟩
    exact
      ⟨emb, source,
        (nonempty_planarBoundaryCanonicalWitnessChoice_iff_facewiseAtMostOneInteriorEdge_of_closedWalkAnnulusBoundarySource
          source).2 hAtMost⟩

end Mettapedia.GraphTheory.FourColor
