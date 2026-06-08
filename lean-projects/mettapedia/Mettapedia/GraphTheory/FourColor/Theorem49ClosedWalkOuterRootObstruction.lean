import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryOuterBoundaryRootInteriorDual
import Mettapedia.GraphTheory.FourColor.Theorem49Synthesis

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- If the annulus boundary split is the honest split extracted from a closed-walk
boundary source, then an adjacency-distance peel whose roots all meet the extracted outer
boundary is impossible.

The point is structural: inner-boundary faces are disjoint from the peeled interior, hence the
root-distance package forces them to be root faces; if every root touches the outer boundary,
the same face lies in both extracted boundary-face layers, contradicting the closed-walk
source's boundary-component separation. -/
theorem false_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hrootsOuterBoundary : ∀ r ∈ interiorData.roots,
      ∃ e ∈ emb.faceBoundary r.1,
        e ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) :
    False := by
  let data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb :=
    { boundaryData := source.toPlanarBoundaryAnnulusBoundaryData
      interiorData := interiorData
      hrootsOuterBoundary := hrootsOuterBoundary }
  rcases data.boundaryData.innerBoundaryFaces_nonempty with ⟨f, hfInner⟩
  have hfOuter : f ∈ data.boundaryData.outerBoundaryFaces :=
    data.mem_outerBoundaryFaces_of_mem_innerBoundaryFaces hfInner
  exact
    (Finset.disjoint_left.mp source.outerBoundaryFaces_disjoint_innerBoundaryFaces)
      hfOuter hfInner

/-- Same obstruction stated directly for the current outer-boundary-rooted annulus data: it cannot
share its boundary split with a closed-walk annulus-boundary source on the same embedding. -/
theorem false_of_closedWalkAnnulusBoundarySource_and_outerBoundaryRootAdjDistancePeelData_sameBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData) :
    False := by
  exact
    false_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterBoundary
      source data.interiorData
      (by
        intro r hr
        rcases data.hrootsOuterBoundary r hr with ⟨e, hef, heOuter⟩
        exact ⟨e, hef, by simpa [hboundary] using heOuter⟩)

/-- Existential form of the closed-walk/outer-root incompatibility on a fixed embedding. -/
theorem not_exists_closedWalkAnnulusBoundarySource_and_outerBoundaryRootAdjDistancePeelData_sameBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    ¬ (∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
          data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData) := by
  rintro ⟨source, data, hboundary⟩
  exact
    false_of_closedWalkAnnulusBoundarySource_and_outerBoundaryRootAdjDistancePeelData_sameBoundaryData
      source data hboundary

/-- Graph-level obstruction: the honest closed-walk boundary source cannot be combined with the
current all-roots-on-the-outer-boundary Theorem 4.9 data when both use the same annulus boundary
split. -/
theorem not_exists_embedding_closedWalkAnnulusBoundarySource_and_outerBoundaryRootAdjDistancePeelData_sameBoundaryData
    {G : SimpleGraph V} :
    ¬ (∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
            data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData) := by
  rintro ⟨_emb, source, data, hboundary⟩
  exact
    false_of_closedWalkAnnulusBoundarySource_and_outerBoundaryRootAdjDistancePeelData_sameBoundaryData
      source data hboundary

/-- The same honest-source obstruction already kills the stronger outer-boundary-rooted canonical
parent package: once the source and the parent data use the same extracted annulus boundary split,
an inner-boundary face is simultaneously forced into the outer-boundary face layer. -/
theorem false_of_closedWalkAnnulusBoundarySource_and_outerBoundaryRootParentPeelData_sameBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryOuterBoundaryRootParentPeelData emb)
    (hboundary :
      data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData) :
    False := by
  rcases source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces_nonempty with ⟨f, hfInner⟩
  have hfInner' : f ∈ data.boundaryData.innerBoundaryFaces := by
    simpa [hboundary] using hfInner
  have hfOuter' : f ∈ data.boundaryData.outerBoundaryFaces :=
    data.mem_outerBoundaryFaces_of_mem_innerBoundaryFaces hfInner'
  have hfOuter : f ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces := by
    simpa [hboundary] using hfOuter'
  exact
    (Finset.disjoint_left.mp source.outerBoundaryFaces_disjoint_innerBoundaryFaces)
      hfOuter hfInner

/-- Fixed-embedding nonexistence form of the stronger outer-boundary-rooted parent obstruction. -/
theorem not_exists_closedWalkAnnulusBoundarySource_and_outerBoundaryRootParentPeelData_sameBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    ¬ (∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryOuterBoundaryRootParentPeelData emb,
          data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData) := by
  rintro ⟨source, data, hboundary⟩
  exact
    false_of_closedWalkAnnulusBoundarySource_and_outerBoundaryRootParentPeelData_sameBoundaryData
      source data hboundary

/-- Graph-level form of the stronger outer-boundary-rooted parent obstruction. -/
theorem not_exists_embedding_closedWalkAnnulusBoundarySource_and_outerBoundaryRootParentPeelData_sameBoundaryData
    {G : SimpleGraph V} :
    ¬ (∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
          ∃ data : PlanarBoundaryOuterBoundaryRootParentPeelData emb,
            data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData) := by
  rintro ⟨_emb, source, data, hboundary⟩
  exact
    false_of_closedWalkAnnulusBoundarySource_and_outerBoundaryRootParentPeelData_sameBoundaryData
      source data hboundary

/-- The preceding positive outer-root non-vacuity route is vacuous on the honest same-split
closed-walk source surface: the required root-localization witness already contradicts the
source's own extracted annulus boundary split, so no same-embedding instance of that hypothesis
package exists. -/
theorem
    not_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_rootsOuterAmbientBoundary_and_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} :
    ¬ (∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        ∃ hrootsOuterBoundary : ∀ r ∈ interiorData.roots,
          ∃ e ∈ emb.faceBoundary r.1,
            e ∈ source.boundaryReachability.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary,
          let data :=
            planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary
              source.boundaryReachability interiorData hrootsOuterBoundary
          (∀ f ∈
            (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
              data).peelFaces,
            Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
              (edgeEndpointSupport
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
          (interiorEdgeEndpointSupport emb).Nonempty) := by
  rintro ⟨emb, source, interiorData, hrootsOuterBoundary, _hPeelNoTouch, _hRawCarrier⟩
  have hrootsOuterBoundary' : ∀ r ∈ interiorData.roots,
      ∃ e ∈ emb.faceBoundary r.1,
        e ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary := by
    intro r hr
    simpa using hrootsOuterBoundary r hr
  exact
    false_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterBoundary
      source interiorData hrootsOuterBoundary'

/-- The outer-boundary-root non-vacuous synthesis endpoint cannot coexist with the honest
closed-walk annulus source when both use the same extracted annulus boundary split. The
incompatibility is already in the route data; the synthesis witness itself adds no escape hatch.
-/
theorem
    not_exists_closedWalkAnnulusBoundarySource_and_theorem49OuterBoundaryRootNonemptySynthesis_sameBoundaryData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (C₀ : G.EdgeColoring Color) :
    ¬ (∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
          data.boundaryData = source.toPlanarBoundaryAnnulusBoundaryData ∧
          Theorem49OuterBoundaryRootNonemptySynthesis emb data C₀) := by
  rintro ⟨emb, source, data, hboundary, _hsynth⟩
  exact
    false_of_closedWalkAnnulusBoundarySource_and_outerBoundaryRootAdjDistancePeelData_sameBoundaryData
      source data hboundary

end Mettapedia.GraphTheory.FourColor
