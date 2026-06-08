import Mettapedia.GraphTheory.FourColor.Theorem49RootedDistance

namespace Mettapedia.GraphTheory.FourColor

variable {V F : Type*} [DecidableEq V] [DecidableEq F]

/-- The faces lying in strictly later layers than `i`. This is the unpeeled remainder after
removing the first `i + 1` collars in an outside-in peeling process. -/
def laterLayerFaces {n : ℕ} (layerFaces : Fin n → Finset F) (i : Fin n) : Finset F :=
  (Finset.univ.filter fun j : Fin n => i < j).biUnion layerFaces

theorem mem_laterLayerFaces_iff {n : ℕ} (layerFaces : Fin n → Finset F) (i : Fin n) {f : F} :
    f ∈ laterLayerFaces layerFaces i ↔ ∃ j : Fin n, i < j ∧ f ∈ layerFaces j := by
  unfold laterLayerFaces
  constructor
  · intro hf
    rcases Finset.mem_biUnion.1 hf with ⟨j, hj, hjf⟩
    exact ⟨j, (Finset.mem_filter.1 hj).2, hjf⟩
  · rintro ⟨j, hij, hjf⟩
    exact Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩, hjf⟩

theorem layerFaces_subset_laterLayerFaces_of_lt {n : ℕ} (layerFaces : Fin n → Finset F)
    {i j : Fin n} (hij : i < j) :
    layerFaces j ⊆ laterLayerFaces layerFaces i := by
  intro f hf
  exact (mem_laterLayerFaces_iff layerFaces i).2 ⟨j, hij, hf⟩

theorem laterLayerFaces_subset_laterLayerFaces_of_lt {n : ℕ} (layerFaces : Fin n → Finset F)
    {i j : Fin n} (hij : i < j) :
    laterLayerFaces layerFaces j ⊆ laterLayerFaces layerFaces i := by
  intro f hf
  rcases (mem_laterLayerFaces_iff layerFaces j).1 hf with ⟨k, hjk, hk⟩
  exact (mem_laterLayerFaces_iff layerFaces i).2 ⟨k, lt_trans hij hjk, hk⟩

theorem laterLayerFaces_eq_empty_of_forall_not_lt {n : ℕ}
    (layerFaces : Fin n → Finset F) (i : Fin n)
    (hi : ∀ j : Fin n, ¬ i < j) :
    laterLayerFaces layerFaces i = ∅ := by
  ext f
  constructor
  · intro hf
    rcases (mem_laterLayerFaces_iff layerFaces i).1 hf with ⟨j, hij, _⟩
    exact False.elim (hi j hij)
  · intro hf
    simp at hf

/-- The boundary of the still-unpeeled suffix of layers after stage `i`, computed relative to that
suffix rather than the whole ambient face set. This is the formal "current frontier" in the paper's
outside-in collar peeling. -/
def laterLayerBoundarySupport {G : SimpleGraph V} {n : ℕ}
    (faceBoundary : F → Finset G.edgeSet) (layerFaces : Fin n → Finset F) (i : Fin n) :
    Finset G.edgeSet :=
  relativeBoundarySupport faceBoundary (laterLayerFaces layerFaces i)

/-- Stronger collar-layer witness-cover data that records the actual frontier geometry of an
outside-in peel. For a face in layer `i`, every non-witness edge lies either on the ambient
boundary or on the relative boundary of the deeper remainder; every such deeper-frontier edge is
required to be the witness edge of some strictly later layer. This is closer to the paper's Step 2
than the weaker global collar package. -/
structure RelativeBoundaryCollarLayerFacePeelWitnessData {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) where
  numLayers : ℕ
  layerFaces : Fin numLayers → Finset F
  witnessEdge : F → G.edgeSet
  hdisjoint : ∀ {i j : Fin numLayers}, i ≠ j → Disjoint (layerFaces i) (layerFaces j)
  hcover : interiorEdgeSupport faceBoundary allFaces ⊆
    (Finset.univ.biUnion layerFaces).image witnessEdge
  hwitness : ∀ i f, f ∈ layerFaces i → witnessEdge f ∈ faceBoundary f
  hrest : ∀ i f, f ∈ layerFaces i → ∀ e ∈ (faceBoundary f).erase (witnessEdge f),
    e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
      e ∈ laterLayerBoundarySupport faceBoundary layerFaces i
  hfrontier : ∀ i e, e ∈ laterLayerBoundarySupport faceBoundary layerFaces i →
    ∃ j : Fin numLayers, i < j ∧ ∃ g ∈ layerFaces j, witnessEdge g = e

/-- The stronger relative-boundary collar package canonically lowers to the weaker generic
collar-layer witness-cover interface already consumed by Theorem 4.9. -/
noncomputable def
    RelativeBoundaryCollarLayerFacePeelWitnessData.toCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : RelativeBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary) :
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
  rcases data.hrest i f hfi e he with hboundary | hfrontier
  · exact Or.inl hboundary
  · rcases data.hfrontier i e hfrontier with ⟨j, hij, g, hgj, hge⟩
    exact Or.inr ⟨j, hij, g, hgj, hge⟩

/-- Certificate form of the stronger relative-boundary collar interface. -/
noncomputable def
    RelativeBoundaryCollarLayerFacePeelWitnessData.toBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V} {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : RelativeBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary) :
    BoundaryRootedFacePeelCertificate allFaces faceBoundary :=
  data.toCollarLayerFacePeelWitnessData.toBoundaryRootedFacePeelCertificate

/-- Annihilator form of the stronger relative-boundary collar interface. This is the theorem-layer
endpoint that matches an actual collar-by-collar geometric peeling. -/
theorem zero_on_ambientFaceSupport_of_relativeBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (data : RelativeBoundaryCollarLayerFacePeelWitnessData allFaces faceBoundary)
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
