import Mettapedia.GraphTheory.FourColor.Theorem49RelativeBoundaryCollar

namespace Mettapedia.GraphTheory.FourColor

variable {V F : Type*} [DecidableEq V] [DecidableEq F]

/-- Stronger collar-layer witness-cover data that stores the actual remainder face set after each
peeled layer. This matches the paper's outside-in annulus decomposition more closely than the
plain relative-boundary package: each stage explicitly names the still-unpeeled suffix of faces,
and the local frontier condition is stated directly on that remainder. -/
structure RemainderBoundaryCollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) where
  numLayers : ℕ
  layerFaces : Fin numLayers → Finset F
  remainderFaces : Fin numLayers → Finset F
  witnessEdge : F → G.edgeSet
  hdisjoint : ∀ {i j : Fin numLayers}, i ≠ j -> Disjoint (layerFaces i) (layerFaces j)
  hcover : interiorEdgeSupport faceBoundary allFaces ⊆
    (Finset.univ.biUnion layerFaces).image witnessEdge
  hwitness : ∀ i f, f ∈ layerFaces i -> witnessEdge f ∈ faceBoundary f
  hremainder : ∀ i, remainderFaces i = laterLayerFaces layerFaces i
  hrest : ∀ i f, f ∈ layerFaces i → ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
    e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
      e ∈ relativeBoundarySupport faceBoundary (remainderFaces i)
  hfrontier : ∀ i e, e ∈ relativeBoundarySupport faceBoundary (remainderFaces i) →
    ∃ j : Fin numLayers, i < j ∧ ∃ g ∈ layerFaces j, witnessEdge g = e

/-- A relative-boundary collar package canonically upgrades to the explicit-remainder package by
recording the deeper suffix of layers as the remainder at each stage. -/
def RelativeBoundaryCollarLayerFacePeelWitnessData.toRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : RelativeBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary) :
    RemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary := by
  refine
    { numLayers := data.numLayers
      layerFaces := data.layerFaces
      remainderFaces := laterLayerFaces data.layerFaces
      witnessEdge := data.witnessEdge
      hdisjoint := data.hdisjoint
      hcover := data.hcover
      hwitness := data.hwitness
      hremainder := ?_
      hrest := ?_
      hfrontier := ?_ }
  · intro i
    rfl
  · intro i f hfi e he
    rcases data.hrest i f hfi e he with hboundary | hlater
    · exact Or.inl hboundary
    · exact Or.inr <| by simpa [laterLayerBoundarySupport]
      using hlater
  · intro i e he
    simpa [laterLayerBoundarySupport] using data.hfrontier i e he

/-- Forgetting the explicit remainder sequence recovers the relative-boundary collar package. -/
def RemainderBoundaryCollarLayerFacePeelWitnessData.toRelativeBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : RemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary) :
    RelativeBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary := by
  refine
    { numLayers := data.numLayers
      layerFaces := data.layerFaces
      witnessEdge := data.witnessEdge
      hdisjoint := data.hdisjoint
      hcover := data.hcover
      hwitness := data.hwitness
      hrest := ?_
      hfrontier := ?_ }
  · intro i f hfi e he
    rcases data.hrest i f hfi e he with hboundary | hrem
    · exact Or.inl hboundary
    · exact Or.inr <| by
        simpa [laterLayerBoundarySupport, data.hremainder i] using hrem
  · intro i e he
    have hrem : e ∈ relativeBoundarySupport faceBoundary (data.remainderFaces i) := by
      simpa [laterLayerBoundarySupport, data.hremainder i] using he
    exact data.hfrontier i e hrem

/-- Certificate form of the explicit-remainder collar interface. -/
noncomputable def RemainderBoundaryCollarLayerFacePeelWitnessData.toBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : RemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary :=
  data.toRelativeBoundaryCollarLayerFacePeelWitnessData.toBoundaryRootedFacePeelCertificate

/-- Annihilator form of the explicit-remainder collar interface. -/
theorem zero_on_ambientFaceSupport_of_remainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (data : RemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary)
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
  exact zero_on_ambientFaceSupport_of_relativeBoundaryCollarLayerFacePeelWitnessData
    (C := C) (htait := htait) (z := z) (allFaces := allFaces) (faceBoundary := faceBoundary)
    (data := data.toRelativeBoundaryCollarLayerFacePeelWitnessData)
    hall hzeroBoundary horth

end Mettapedia.GraphTheory.FourColor
