import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryFreeSelectorPositiveRoute
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSourceProjection
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryCollarPeeling
import Mettapedia.GraphTheory.FourColor.Theorem49SpanningGap
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryFaceIncidence

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph
open Theorem49ForcingInteriorEdgeObstruction

variable {V F : Type*} [DecidableEq V] [DecidableEq F]

/-- Residual/current-boundary peeling data. The present implementation is intentionally thin: it
reuses the already formalized local explicit-remainder collar package and exposes the residual
boundary as the union of selected ambient boundary support with the relative boundary of the
current remainder. -/
abbrev ResidualBoundaryLayerFacePeelWitnessData {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) :=
  LocalRemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary

def ResidualBoundaryLayerFacePeelWitnessData.currentBoundary
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary)
    (i : Fin data.numLayers) : Finset G.edgeSet :=
  selectedBoundarySupport faceBoundary allFaces allFaces ∪
    relativeBoundarySupport faceBoundary (data.remainderFaces i)

theorem ResidualBoundaryLayerFacePeelWitnessData.mem_currentBoundary_of_mem_selectedBoundary
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary)
    {i : Fin data.numLayers} {e : G.edgeSet}
    (he :
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces) :
    e ∈ data.currentBoundary i := by
  exact Finset.mem_union.2 (Or.inl he)

theorem ResidualBoundaryLayerFacePeelWitnessData.mem_currentBoundary_of_mem_relativeBoundary
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary)
    {i : Fin data.numLayers} {e : G.edgeSet}
    (he :
      e ∈ relativeBoundarySupport faceBoundary (data.remainderFaces i)) :
    e ∈ data.currentBoundary i := by
  exact Finset.mem_union.2 (Or.inr he)

theorem
    ResidualBoundaryLayerFacePeelWitnessData.currentBoundary_or_laterWitness_of_hrest
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary)
    {i : Fin data.numLayers} {f : F}
    (hf : f ∈ data.layerFaces i)
    {e : G.edgeSet} (he : e ∈ (faceBoundary f).erase (data.witnessEdge f)) :
    e ∈ data.currentBoundary i ∨
      ∃ j : Fin data.numLayers, i < j ∧ ∃ g ∈ data.layerFaces j,
        data.witnessEdge g = e := by
  rcases data.hrest i f hf e he with hboundary | ⟨j, hij, g, hgj, hge, hrel⟩
  · exact Or.inl (data.mem_currentBoundary_of_mem_selectedBoundary hboundary)
  · exact Or.inr ⟨j, hij, g, hgj, hge⟩

theorem ResidualBoundaryLayerFacePeelWitnessData.laterWitness_mem_currentBoundary_of_hrest
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary)
    {i : Fin data.numLayers} {f : F}
    (hf : f ∈ data.layerFaces i)
    {e : G.edgeSet} (he : e ∈ (faceBoundary f).erase (data.witnessEdge f))
    (_hg :
      ∃ j : Fin data.numLayers, i < j ∧ ∃ g' ∈ data.layerFaces j,
        data.witnessEdge g' = e) :
    e ∈ data.currentBoundary i := by
  rcases data.hrest i f hf e he with hboundary | ⟨j, hij, g', hgj, hge, hrel⟩
  · exact data.mem_currentBoundary_of_mem_selectedBoundary hboundary
  · exact data.mem_currentBoundary_of_mem_relativeBoundary hrel

/-- In residual/current-boundary witness data, every non-witness remainder edge on a peeled face
already lies on the live current boundary at that layer. This is the direct residual-boundary
analogue of the terminal selected-boundary remainder lemmas used elsewhere in the theorem-4.9
route. -/
theorem ResidualBoundaryLayerFacePeelWitnessData.mem_currentBoundary_of_mem_erase
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary)
    {i : Fin data.numLayers} {f : F}
    (hf : f ∈ data.layerFaces i)
    {e : G.edgeSet} (he : e ∈ (faceBoundary f).erase (data.witnessEdge f)) :
    e ∈ data.currentBoundary i := by
  rcases data.currentBoundary_or_laterWitness_of_hrest hf he with hcurrent | hlater
  · exact hcurrent
  · exact data.laterWitness_mem_currentBoundary_of_hrest hf he hlater

theorem ResidualBoundaryLayerFacePeelWitnessData.erase_subset_currentBoundary
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary)
    {i : Fin data.numLayers} {f : F}
    (hf : f ∈ data.layerFaces i) :
    (faceBoundary f).erase (data.witnessEdge f) ⊆ data.currentBoundary i := by
  intro e he
  exact data.mem_currentBoundary_of_mem_erase hf he

theorem
    ResidualBoundaryLayerFacePeelWitnessData.exists_layer_face_currentBoundary_remainders_of_mem_interiorEdgeSupport
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport faceBoundary allFaces) :
    ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
      data.witnessEdge f = e ∧
      ∀ e' ∈ (faceBoundary f).erase (data.witnessEdge f), e' ∈ data.currentBoundary i := by
  rcases Finset.mem_image.1 (data.hcover he) with ⟨f, hf, hfe⟩
  rcases Finset.mem_biUnion.1 hf with ⟨i, _hi, hfi⟩
  exact ⟨i, f, hfi, hfe, fun e' he' => data.mem_currentBoundary_of_mem_erase hfi he'⟩

theorem
    ResidualBoundaryLayerFacePeelWitnessData.exists_layer_face_currentBoundary_remainders_of_interiorEdgeSupport_nonempty
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary)
    (hInterior : (interiorEdgeSupport faceBoundary allFaces).Nonempty) :
    ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
      ∀ e ∈ (faceBoundary f).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  rcases hInterior with ⟨e, he⟩
  rcases
    data.exists_layer_face_currentBoundary_remainders_of_mem_interiorEdgeSupport he with
    ⟨i, f, hfi, _hfe, hremainders⟩
  exact ⟨i, f, hfi, hremainders⟩

def LocalRemainderBoundaryCollarLayerFacePeelWitnessData.toResidualBoundaryLayerFacePeelWitnessData
    {G : SimpleGraph V} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : LocalRemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary) :
    ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary :=
  data

def RemainderBoundaryCollarLayerFacePeelWitnessData.toResidualBoundaryLayerFacePeelWitnessData
    {G : SimpleGraph V} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : RemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary)
    (hlayerSubset : ∀ i, data.layerFaces i ⊆ allFaces) :
    ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary :=
  data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData hlayerSubset

def CollarLayerFacePeelWitnessData.toResidualBoundaryLayerFacePeelWitnessData
    {G : SimpleGraph V} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : CollarLayerFacePeelWitnessData allFaces faceBoundary)
    (hlayerSubset : ∀ i, data.layerFaces i ⊆ allFaces)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary :=
  data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData hlayerSubset hall

/-- Embedding-facing residual/current-boundary witness data. -/
abbrev PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :=
  ResidualBoundaryLayerFacePeelWitnessData emb.faces.attach
    (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)

/-- Forget the boundary-aware collar layer to the generic attached-face collar interface. -/
noncomputable def
    genericCollarLayerFacePeelWitnessData_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb) :
    CollarLayerFacePeelWitnessData emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) := by
  refine
    { numLayers := data.numLayers
      layerFaces := data.layerFaces
      witnessEdge := data.witnessEdge
      hdisjoint := data.hdisjoint
      hcover := ?_
      hwitness := ?_
      hrest := ?_ }
  · simpa [interiorEdgeSupport_ambientFaceBoundary_eq
      (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using data.hcover
  · intro i f hf
    simpa [ambientFaceBoundary] using data.hwitness i f hf
  · intro i f hf e he
    rcases data.hrest i f hf e (by simpa [ambientFaceBoundary] using he) with
      hboundary | ⟨j, hij, g, hgj, hge⟩
    · exact Or.inl <| by
        simpa [selectedBoundarySupport_ambientFaceBoundary_eq
          (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using hboundary
    · exact Or.inr ⟨j, hij, g, hgj, hge⟩

noncomputable def
    PlanarBoundaryCollarLayerFacePeelWitnessData.toResidualBoundaryLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb) :
    PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb := by
  let generic :=
    genericCollarLayerFacePeelWitnessData_of_planarBoundaryCollarLayerFacePeelWitnessData data
  have hall :
      ∀ e,
        totalIncidenceCount
            (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
            emb.faces.attach e ≤ 2 := by
    intro e
    simpa [totalIncidenceCount_ambientFaceBoundary_eq
      (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using
      planeEmbeddingWithBoundary_totalIncidenceCount_le_two emb e
  exact
    generic.toResidualBoundaryLayerFacePeelWitnessData
      (hlayerSubset := by
        intro _ f _hf
        exact Finset.mem_attach _ _)
      hall

noncomputable def PlanarBoundaryAnnulusConstruction.toResidualBoundaryLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb) :
    PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb :=
  data.toPlanarBoundaryCollarLayerFacePeelWitnessData.toResidualBoundaryLayerFacePeelWitnessData

theorem
    nonempty_planarBoundaryResidualBoundaryLayerFacePeelWitnessData_iff_nonempty_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb) ↔
      Nonempty (PlanarBoundaryCollarLayerFacePeelWitnessData emb) := by
  constructor
  · rintro ⟨data⟩
    exact
      ⟨planarBoundaryCollarLayerFacePeelWitnessData_of_genericLocalRemainderBoundaryCollarLayerFacePeelWitnessData
        data⟩
  · rintro ⟨data⟩
    exact ⟨data.toResidualBoundaryLayerFacePeelWitnessData⟩

theorem
    zero_on_ambientFaceSupport_of_residualBoundaryLayerFacePeelWitnessData_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (data : ResidualBoundaryLayerFacePeelWitnessData allFaces faceBoundary)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ i f, f ∈ data.layerFaces i →
      ∀ γ, γ ≠ 0 → γ ≠ C (data.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (data.witnessEdge f)) (C (data.witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (data.witnessEdge f)) (C (data.witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact
    zero_on_ambientFaceSupport_of_localRemainderBoundaryCollarLayerFacePeelWitnessData
      C htait z allFaces faceBoundary data hall hzeroBoundary horth

theorem boundaryZeroAnnihilatorTrivialForEmbedding_of_residualBoundaryLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀ := by
  exact
    boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_residualBoundaryLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      (planarBoundaryCollarLayerFacePeelWitnessData_of_genericLocalRemainderBoundaryCollarLayerFacePeelWitnessData
        data)
      C₀ hC₀ hCarrier

theorem
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_residualBoundaryLayerFacePeelWitnessData
      data C₀ hC₀
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint)

/-- Local endpoint form of the same residual/current-boundary witness-face diagnostic. -/
theorem
    exists_layerFace_currentBoundary_remainders_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
      ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  have hInterior :
      (interiorEdgeSupport
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary)
        emb.faces.attach).Nonempty := by
    simpa [interiorEdgeSupport_ambientFaceBoundary_eq
      (faceBoundary := emb.faceBoundary) (allFaces := emb.faces)] using
      interiorEdgeSupport_nonempty_of_hasUnblockedInteriorEndpoint hEndpoint
  rcases
    data.exists_layer_face_currentBoundary_remainders_of_interiorEdgeSupport_nonempty hInterior with
    ⟨i, f, hfi, hremainders⟩
  exact ⟨i, f, hfi, by
    simpa [ambientFaceBoundary] using hremainders⟩

/-- A residual/current-boundary witness package together with the purified nonempty carrier
already exhibits a peeled layer face whose non-witness remainders lie on the live current
boundary at that layer. -/
theorem exists_layerFace_currentBoundary_remainders_of_residualBoundaryLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    ∃ i : Fin data.numLayers, ∃ f ∈ data.layerFaces i,
      ∀ e ∈ (emb.faceBoundary f.1).erase (data.witnessEdge f), e ∈ data.currentBoundary i := by
  have hEndpoint :
      HasUnblockedInteriorEndpoint emb :=
    (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
      emb).2 hCarrier
  exact
    exists_layerFace_currentBoundary_remainders_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data hEndpoint

/-- Fixed-embedding positive route using residual/current-boundary witness data and a surviving
purified endpoint carrier. -/
def Theorem49ResidualBoundaryPositiveProjectedGeometryOn {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∃ _data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb,
    (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_residualBoundaryPositiveProjectedGeometryOn
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (geom : Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases geom with ⟨data, hCarrier⟩
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_residualBoundaryLayerFacePeelWitnessData
      data C₀ hC₀ hCarrier

theorem theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    ⟨data,
      (hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).1 hEndpoint⟩

theorem theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData hEndpoint

theorem theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ↔
      Theorem49CollarLayerPositiveProjectedGeometryOn emb := by
  constructor
  · rintro ⟨data, hCarrier⟩
    exact
      ⟨planarBoundaryCollarLayerFacePeelWitnessData_of_genericLocalRemainderBoundaryCollarLayerFacePeelWitnessData
        data, hCarrier⟩
  · rintro ⟨data, hCarrier⟩
    exact ⟨data.toResidualBoundaryLayerFacePeelWitnessData, hCarrier⟩

theorem theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_heightOrderedPositiveProjectedGeometryOn
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb ↔
      Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  constructor
  · intro hResidual
    exact
      (heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn).2
        ((theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn).1
          hResidual)
  · intro hHeight
    exact
      (theorem49ResidualBoundaryPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn).2
        ((heightOrderedPositiveProjectedGeometryOn_iff_collarLayerPositiveProjectedGeometryOn).1
          hHeight)

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_residualBoundaryPositiveProjectedGeometryOn
      (theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_annulusCollarGeometry_and_hasUnblockedInteriorEndpoint
        data hEndpoint)
      C₀ hC₀

/-- Selector-facing residual/current-boundary route data. This is the strict-descent selector
surface together with the chosen annulus boundary split and witness/height functions. -/
structure ResidualBoundarySelectorData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  boundaryData : PlanarBoundaryAnnulusBoundaryData emb
  selector : BoundaryFreeIncidentFaceSelector emb
  fallbackEdge : AmbientFace emb.faces → G.edgeSet
  faceDistance : AmbientFace emb.faces → ℕ
  hinjective :
    ∀ {e₁ e₂ : G.edgeSet}
      (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
      (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
        selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂
  hrest :
    ∀ f ∈ selector.peelFaces,
      ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
        e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
          ∃ g ∈ selector.peelFaces,
            selector.selectedWitnessEdge fallbackEdge g = e ∧
              faceDistance f < faceDistance g

noncomputable def ResidualBoundarySelectorData.toPlanarBoundaryAnnulusConstruction
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : ResidualBoundarySelectorData emb) :
    PlanarBoundaryAnnulusConstruction emb :=
  data.selector.toPlanarBoundaryAnnulusConstruction
    data.boundaryData data.fallbackEdge data.faceDistance data.hinjective data.hrest

noncomputable def ResidualBoundarySelectorData.toResidualBoundaryLayerFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : ResidualBoundarySelectorData emb) :
    PlanarBoundaryResidualBoundaryLayerFacePeelWitnessData emb :=
  data.toPlanarBoundaryAnnulusConstruction.toResidualBoundaryLayerFacePeelWitnessData

/-- Canonical residual/current-boundary selector package extracted from generic boundary-root
parent peel data.  This repackages the already proved strict-descent selector surface into the
residual-boundary interface. -/
noncomputable def residualBoundarySelectorData_of_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :
    ResidualBoundarySelectorData emb where
  boundaryData := boundaryData
  selector := boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data
  fallbackEdge := data.fallbackEdge
  faceDistance := fun f =>
    (interiorDualSpanningForest emb.faceBoundary emb.faces).dist f
      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
        data.roots data.hcoverRoots data.hsepRoots f)
  hinjective :=
    boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_injective data
  hrest := by
    simpa using
      boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_strictDescent
        boundaryData data

/-- Annulus-root parent peel data canonically determines residual/current-boundary selector
data on the same embedding. -/
noncomputable def residualBoundarySelectorData_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb) :
    ResidualBoundarySelectorData emb :=
  residualBoundarySelectorData_of_interiorDualBoundaryRootParentPeelData
    data.boundaryData data.interiorData

/-- The degenerate no-interior-edge closed-walk source branch already determines residual/current
boundary selector data on the same embedding. -/
theorem nonempty_residualBoundarySelectorData_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    Nonempty (ResidualBoundarySelectorData emb) := by
  exact
    ⟨residualBoundarySelectorData_of_interiorDualBoundaryRootParentPeelData
      source.toPlanarBoundaryAnnulusBoundaryData
      (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
        source hcoverRoots hsepRoots hnoInterior)⟩

/-- The stronger source-fixed raw canonical-parent shared-edge-cover shell also reaches the
residual/current-boundary selector surface, but only through the no-interior-edge branch forced
by the current honest closed-walk source semantics. -/
theorem nonempty_residualBoundarySelectorData_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge)) :
    Nonempty (ResidualBoundarySelectorData emb) := by
  exact
    nonempty_residualBoundarySelectorData_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      source hcoverRoots hsepRoots
      (interiorEdgeSupport_eq_empty_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover)

/-- Graph-level residual/current-boundary selector lowering for the honest closed-walk raw
canonical-parent shared-edge-cover shell. -/
theorem exists_embedding_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_residualBoundarySelectorData_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge) ∧
        Nonempty (ResidualBoundarySelectorData emb) := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
      nonempty_residualBoundarySelectorData_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover⟩

/-- The actual theorem-4.9 boundary-order raw canonical-parent shared-edge-cover shell also
reaches the residual/current-boundary selector surface, but only because the induced closed-walk
source already lies in the forced no-interior-edge branch. -/
theorem nonempty_residualBoundarySelectorData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge)) :
    Nonempty (ResidualBoundarySelectorData emb) := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    nonempty_residualBoundarySelectorData_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover

/-- Graph-level residual/current-boundary selector lowering for the actual theorem-4.9
boundary-order raw canonical-parent shared-edge-cover shell. -/
theorem exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_residualBoundarySelectorData_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        Nonempty (ResidualBoundarySelectorData emb) := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover,
      nonempty_residualBoundarySelectorData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover⟩

theorem theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      (residualBoundarySelectorData_of_interiorDualBoundaryRootParentPeelData
        boundaryData data |>.toResidualBoundaryLayerFacePeelWitnessData)
      hEndpoint

theorem theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      data.boundaryData data.interiorData hEndpoint

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  let selectorData :=
    residualBoundarySelectorData_of_interiorDualBoundaryRootParentPeelData
      boundaryData data
  exact
    selectorData.selector.theorem49BoundaryRootNonemptyProjectedSynthesis_of_strictDescent_and_hasUnblockedInteriorEndpoint
      selectorData.boundaryData selectorData.fallbackEdge selectorData.faceDistance
      selectorData.hinjective selectorData.hrest hEndpoint C₀ hC₀

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_planarBoundaryAnnulusRootParentPeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      data.boundaryData data.interiorData hEndpoint C₀ hC₀

theorem theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint
      source.toPlanarBoundaryAnnulusBoundaryData
      (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover)
      hEndpoint

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_interiorDualBoundaryRootParentPeelData_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source.toPlanarBoundaryAnnulusBoundaryData
      (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover)
      hEndpoint C₀ hC₀

theorem theorem49BoundaryRawQuotientErrorPackage_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hEndpoint C₀ hC₀).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

theorem theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hEndpoint

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      hEndpoint C₀ hC₀

theorem theorem49BoundaryRawQuotientErrorPackage_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hEndpoint C₀ hC₀).rawKirchhoffRepresentative_and_boundaryKernelDecomposition
      hx

theorem theorem49HeightOrderedPositiveProjectedGeometryOn_of_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49HeightOrderedPositiveProjectedGeometryOn emb := by
  exact
    data.selector.theorem49HeightOrderedPositiveProjectedGeometryOn_of_strictDescent_and_hasUnblockedInteriorEndpoint
      data.boundaryData data.fallbackEdge data.faceDistance data.hinjective data.hrest hEndpoint

theorem theorem49BoundaryRootNonemptyProjectedSynthesis_of_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  exact
    data.selector.theorem49BoundaryRootNonemptyProjectedSynthesis_of_strictDescent_and_hasUnblockedInteriorEndpoint
      data.boundaryData data.fallbackEdge data.faceDistance data.hinjective data.hrest
      hEndpoint C₀ hC₀

theorem theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    Theorem49ResidualBoundaryPositiveProjectedGeometryOn emb := by
  exact
    theorem49ResidualBoundaryPositiveProjectedGeometryOn_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data.toResidualBoundaryLayerFacePeelWitnessData hEndpoint

theorem exists_layerFace_currentBoundary_remainders_of_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ i : Fin data.toResidualBoundaryLayerFacePeelWitnessData.numLayers,
      ∃ f ∈ data.toResidualBoundaryLayerFacePeelWitnessData.layerFaces i,
        ∀ e ∈ (emb.faceBoundary f.1).erase
            (data.toResidualBoundaryLayerFacePeelWitnessData.witnessEdge f),
          e ∈ data.toResidualBoundaryLayerFacePeelWitnessData.currentBoundary i := by
  exact
    exists_layerFace_currentBoundary_remainders_of_residualBoundaryLayerFacePeelWitnessData_and_hasUnblockedInteriorEndpoint
      data.toResidualBoundaryLayerFacePeelWitnessData hEndpoint

theorem theorem49BoundaryRawQuotientErrorPackage_of_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : ResidualBoundarySelectorData emb)
    (hEndpoint : HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    Theorem49BoundaryRawQuotientErrorPackage emb C₀ x := by
  exact
    (theorem49BoundaryRootNonemptyProjectedSynthesis_of_residualBoundarySelectorData_and_hasUnblockedInteriorEndpoint
      data hEndpoint C₀ hC₀).rawKirchhoffRepresentative_and_boundaryKernelDecomposition hx

theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge) ∧
        HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior,
      hcover, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
        hEndpoint C₀ hC₀⟩

theorem exists_theorem49BoundaryRootNonemptyProjectedSynthesis_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        HasUnblockedInteriorEndpoint emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptyProjectedSynthesis emb C₀ := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hEndpoint⟩
  exact
    ⟨emb,
      theorem49BoundaryRootNonemptyProjectedSynthesis_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint_via_residualBoundary
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover hEndpoint C₀ hC₀⟩

end Mettapedia.GraphTheory.FourColor
