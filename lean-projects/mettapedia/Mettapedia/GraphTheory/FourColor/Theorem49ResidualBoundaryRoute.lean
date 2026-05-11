import Mettapedia.GraphTheory.FourColor.GoertzelLemma44
import Mettapedia.GraphTheory.FourColor.Theorem49ResidualBoundaryPeeling
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.FourColor.Theorem49PositiveGeometricSourceConstruction

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Minimal residual seed object extracted from the exact v23 Step 2 single-component
purification theorem. -/
structure V23ResidualBoundarySeed {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color) (faceBoundary : Finset G.edgeSet) where
  component_purification :
    ∀ K : (C.bicoloredSubgraph a b).ConnectedComponent,
      v23PolarizedFaceGenerator C a b faceBoundary +
          v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary =
        componentBoundarySlice C a b faceBoundary K

/-- Finite initial residual state: the exact componentwise purification data together with the
already-proved recovery of the downstream boundary-only generator. -/
structure V23ResidualBoundaryInitialState {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (a b : Color) (faceBoundary : Finset G.edgeSet) where
  seed : V23ResidualBoundarySeed C a b faceBoundary
  sum_purification_eq_boundaryOnly :
    Finset.sum (boundaryKempeComponents C a b faceBoundary)
      (fun K : (C.bicoloredSubgraph a b).ConnectedComponent =>
        v23PolarizedFaceGenerator C a b faceBoundary +
          (v23PolarizedFaceGenerator (C.swapOnKempeComponent a b K) a b faceBoundary :
            G.edgeSet → Color)) =
      polarizedFaceGenerator C a b faceBoundary

theorem residualBoundarySeed_of_v23_single_component_purification
    {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) :
    V23ResidualBoundarySeed C a b faceBoundary := by
  exact ⟨fun K => v23_single_component_purification C a b faceBoundary K⟩

theorem residualBoundaryInitialState_of_sum_v23_single_component_purifications_eq_boundaryOnlyGenerator
    {G : SimpleGraph V} (C : G.EdgeColoring Color)
    (a b : Color) (faceBoundary : Finset G.edgeSet) :
    V23ResidualBoundaryInitialState C a b faceBoundary := by
  exact
    ⟨residualBoundarySeed_of_v23_single_component_purification C a b faceBoundary,
      sum_v23_single_component_purifications_eq_boundaryOnlyGenerator C a b faceBoundary⟩

theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (_source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data hEndpoint C₀ hC₀

theorem
    exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint_direct
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ∧
          HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨source⟩, ⟨data⟩, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySource_and_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
        source data hEndpoint C₀ hC₀⟩

namespace Theorem49ResidualBoundaryRoute

open Theorem49PositiveGeometricSourceConstruction

theorem counterEmbedding_residualBoundaryPositiveProjectedGeometryOn :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn
      Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
      Theorem49PlanarBoundaryAnnulusGeometryRegression.counterCollarGeometry
      counterEmbedding_hasUnblockedInteriorEndpoint

theorem counterEmbedding_boundaryRootNonemptyProjectedSynthesis_via_residualBoundary
    [Fintype Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet]
    [FiniteDimensional F2
      (Theorem49PlanarBoundaryAnnulusGeometryRegression.counterGraph.edgeSet → Color)] :
    Theorem49BoundaryRootNonemptyProjectedSynthesis
      Theorem49PlanarBoundaryAnnulusGeometryRegression.counterEmbedding
      counterGraphTaitEdgeColoring := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      Theorem49PlanarBoundaryAnnulusGeometryRegression.counterCollarGeometry
      counterEmbedding_hasUnblockedInteriorEndpoint
      counterGraphTaitEdgeColoring counterGraphTaitEdgeColoring_isTait

end Theorem49ResidualBoundaryRoute

end Mettapedia.GraphTheory.FourColor
