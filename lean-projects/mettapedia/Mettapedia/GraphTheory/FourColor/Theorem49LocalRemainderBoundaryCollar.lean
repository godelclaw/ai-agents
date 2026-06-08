import Mettapedia.GraphTheory.FourColor.Theorem49RemainderBoundaryCollar

namespace Mettapedia.GraphTheory.FourColor

variable {V F : Type*} [DecidableEq V] [DecidableEq F]

/-- A weaker explicit-remainder collar package: every non-witness edge on a peeled face is either
on the ambient boundary, or is already known to be the witness edge of a strictly later face and
lies on the relative boundary of the current remainder. Unlike the stronger remainder-boundary
package, this does not require every remainder-boundary edge to be globally owned by a later
witness edge. -/
structure LocalRemainderBoundaryCollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) where
  numLayers : ℕ
  layerFaces : Fin numLayers → Finset F
  remainderFaces : Fin numLayers → Finset F
  witnessEdge : F → G.edgeSet
  hlayerSubset : ∀ i, layerFaces i ⊆ allFaces
  hdisjoint : ∀ {i j : Fin numLayers}, i ≠ j → Disjoint (layerFaces i) (layerFaces j)
  hcover : interiorEdgeSupport faceBoundary allFaces ⊆
    (Finset.univ.biUnion layerFaces).image witnessEdge
  hwitness : ∀ i f, f ∈ layerFaces i → witnessEdge f ∈ faceBoundary f
  hremainder : ∀ i, remainderFaces i = laterLayerFaces layerFaces i
  hrest : ∀ i f, f ∈ layerFaces i → ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
    e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
      ∃ j : Fin numLayers, i < j ∧ ∃ g ∈ layerFaces j,
        witnessEdge g = e ∧ e ∈ relativeBoundarySupport faceBoundary (remainderFaces i)

/-- The stronger explicit-remainder package canonically lowers to the weaker local version by
forgetting the global frontier-ownership hypothesis. -/
def RemainderBoundaryCollarLayerFacePeelWitnessData.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : RemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary)
    (hlayerSubset : ∀ i, data.layerFaces i ⊆ allFaces) :
    LocalRemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary := by
  refine
    { numLayers := data.numLayers
      layerFaces := data.layerFaces
      remainderFaces := data.remainderFaces
      witnessEdge := data.witnessEdge
      hlayerSubset := hlayerSubset
      hdisjoint := data.hdisjoint
      hcover := data.hcover
      hwitness := data.hwitness
      hremainder := data.hremainder
      hrest := ?_ }
  intro i f hfi e he
  rcases data.hrest i f hfi e he with hboundary | hrem
  · exact Or.inl hboundary
  · rcases data.hfrontier i e hrem with ⟨j, hij, g, hgj, hge⟩
    exact Or.inr ⟨j, hij, g, hgj, hge, hrem⟩

/-- A generic collar-layer package canonically upgrades to the weaker explicit-remainder package
once one knows that every peeled face lies in the ambient face set. The current remainder at stage
`i` is the suffix of strictly later layers, and any later witness edge on a face in layer `i`
automatically lies on the relative boundary of that remainder. -/
def CollarLayerFacePeelWitnessData.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : CollarLayerFacePeelWitnessData allFaces faceBoundary)
    (hlayerSubset : ∀ i, data.layerFaces i ⊆ allFaces)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    LocalRemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary := by
  refine
    { numLayers := data.numLayers
      layerFaces := data.layerFaces
      remainderFaces := laterLayerFaces data.layerFaces
      witnessEdge := data.witnessEdge
      hlayerSubset := hlayerSubset
      hdisjoint := data.hdisjoint
      hcover := data.hcover
      hwitness := data.hwitness
      hremainder := ?_
      hrest := ?_ }
  · intro i
    rfl
  · intro i f hfi e he
    rcases data.hrest i f hfi e he with hboundary | ⟨j, hij, g, hgj, hge⟩
    · exact Or.inl hboundary
    · refine Or.inr ⟨j, hij, g, hgj, hge, ?_⟩
      have hf_all : f ∈ allFaces := hlayerSubset i hfi
      have hg_all : g ∈ allFaces := hlayerSubset j hgj
      have hsubset_remainder : laterLayerFaces data.layerFaces i ⊆ allFaces := by
        intro x hx
        rcases (mem_laterLayerFaces_iff data.layerFaces i).1 hx with ⟨k, hik, hxk⟩
        exact hlayerSubset k hxk
      have hg_remainder : g ∈ laterLayerFaces data.layerFaces i := by
        exact (mem_laterLayerFaces_iff data.layerFaces i).2 ⟨j, hij, hgj⟩
      have hf_not_remainder : f ∉ laterLayerFaces data.layerFaces i := by
        intro hf_remainder
        rcases (mem_laterLayerFaces_iff data.layerFaces i).1 hf_remainder with ⟨k, hik, hfk⟩
        exact (Finset.disjoint_left.1 (data.hdisjoint (Fin.ne_of_lt hik))) hfi hfk
      have hfg : f ≠ g := by
        intro hfg
        subst hfg
        exact hf_not_remainder hg_remainder
      have hef : e ∈ faceBoundary f := (Finset.mem_erase.1 he).2
      have heg : e ∈ faceBoundary g := by
        simpa [hge] using data.hwitness j g hgj
      simpa using
        mem_relativeBoundarySupport_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_mem_of_not_mem
          (faceBoundary := faceBoundary) (allFaces := allFaces)
          (S := laterLayerFaces data.layerFaces i) (hall := hall)
          (hS := hsubset_remainder) (hf := hf_all) (_hg := hg_all) (_hfg := hfg)
          (hef := hef) (heg := heg) (hgS := hg_remainder) (hfS := hf_not_remainder)

/-- Forgetting the explicit remainder sequence and local relative-boundary witnesses recovers the
generic collar-layer interface already consumed by Theorem 4.9. -/
def LocalRemainderBoundaryCollarLayerFacePeelWitnessData.toCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : LocalRemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary) :
    CollarLayerFacePeelWitnessData allFaces faceBoundary := by
  refine
    { numLayers := data.numLayers
      layerFaces := data.layerFaces
      witnessEdge := data.witnessEdge
      hdisjoint := data.hdisjoint
      hcover := data.hcover
      hwitness := data.hwitness
      hrest := ?_ }
  intro i f hfi e he
  rcases data.hrest i f hfi e he with hboundary | ⟨j, hij, g, hgj, hge, _hrel⟩
  · exact Or.inl hboundary
  · exact Or.inr ⟨j, hij, g, hgj, hge⟩

/-- Certificate form of the weaker explicit-remainder collar interface. -/
noncomputable def
    LocalRemainderBoundaryCollarLayerFacePeelWitnessData.toBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : LocalRemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary :=
  data.toCollarLayerFacePeelWitnessData.toBoundaryRootedFacePeelCertificate

/-- Annihilator form of the weaker explicit-remainder collar interface. -/
theorem zero_on_ambientFaceSupport_of_localRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (data : LocalRemainderBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary)
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
  exact zero_on_ambientFaceSupport_of_collarLayerFacePeelWitnessData
    (C := C) (htait := htait) (z := z) (allFaces := allFaces) (faceBoundary := faceBoundary)
    (data := data.toCollarLayerFacePeelWitnessData)
    hall hzeroBoundary horth

end Mettapedia.GraphTheory.FourColor
