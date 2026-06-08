import Mettapedia.GraphTheory.FourColor.Theorem49InteriorSupport

namespace Mettapedia.GraphTheory.FourColor

variable {V F : Type*} [DecidableEq V] [DecidableEq F]

/-- The Theorem 4.9 annihilator argument on the full ambient face-edge support. Under the standard
at-most-two-faces incidence bound, if the ambient boundary support already vanishes and a valid
face peel order covers the ambient interior edge support, then `z` vanishes on every edge lying on
an ambient face. This isolates the remaining geometric input to a covering face peel certificate
plus the boundary-zero hypothesis coming from `W₀(H)`. -/
theorem zero_on_ambientFaceSupport_of_boundary_zero_and_facePeelWitnessCover {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (baseZero : Finset G.edgeSet) (allFaces : Finset F)
    (faceBoundary : F → Finset G.edgeSet) (witnessEdge : F → G.edgeSet) (faceOrder : List F)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆
      facePeelWitnessSupport faceOrder witnessEdge)
    (hzeroBase : ∀ e ∈ baseZero, z e = 0)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (hstep : ∀ l₁ l₂ f, faceOrder = l₁ ++ f :: l₂ →
      witnessEdge f ∈ faceBoundary f ∧
        (faceBoundary f).erase (witnessEdge f) ⊆
          baseZero ∪ facePeelWitnessSupport l₁ witnessEdge)
    (horth : ∀ f ∈ faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  have hinterior :
      ∀ e ∈ interiorEdgeSupport faceBoundary allFaces, z e = 0 :=
    zero_on_interiorEdgeSupport_of_facePeelWitnessCover C htait z baseZero allFaces
      faceBoundary witnessEdge faceOrder hcover hzeroBase hstep horth
  have hdecomp :
      allFaces.biUnion faceBoundary =
        selectedBoundarySupport faceBoundary allFaces allFaces ∪
          interiorEdgeSupport faceBoundary allFaces :=
    biUnion_eq_selectedBoundarySupport_union_interiorEdgeSupport_of_totalIncidenceCount_le_two
      faceBoundary allFaces hall
  intro e he
  have he' :
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∪
        interiorEdgeSupport faceBoundary allFaces := by
    rw [← hdecomp]
    exact he
  rcases Finset.mem_union.1 he' with hboundary | hint
  · exact hzeroBoundary e hboundary
  · exact hinterior e hint

/-- Closed-ambient specialization of the Theorem 4.9 annihilator argument on the full ambient
face-edge support. If every ambient face-edge is incident to exactly two ambient faces, then the
ambient boundary support is empty, so only the auxiliary `baseZero` set and the face-peeling data
remain. -/
theorem zero_on_ambientFaceSupport_of_totalIncidenceCount_eq_two_and_facePeelWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (baseZero : Finset G.edgeSet) (allFaces : Finset F)
    (faceBoundary : F → Finset G.edgeSet) (witnessEdge : F → G.edgeSet) (faceOrder : List F)
    (hcount : ∀ e ∈ allFaces.biUnion faceBoundary, totalIncidenceCount faceBoundary allFaces e = 2)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆
      facePeelWitnessSupport faceOrder witnessEdge)
    (hzeroBase : ∀ e ∈ baseZero, z e = 0)
    (hstep : ∀ l₁ l₂ f, faceOrder = l₁ ++ f :: l₂ →
      witnessEdge f ∈ faceBoundary f ∧
        (faceBoundary f).erase (witnessEdge f) ⊆
          baseZero ∪ facePeelWitnessSupport l₁ witnessEdge)
    (horth : ∀ f ∈ faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  refine zero_on_ambientFaceSupport_of_boundary_zero_and_facePeelWitnessCover
    (C := C) (htait := htait) (z := z) (baseZero := baseZero)
    (allFaces := allFaces) (faceBoundary := faceBoundary)
    (witnessEdge := witnessEdge) (faceOrder := faceOrder)
    (hall := totalIncidenceCount_le_two_of_eq_two_on_biUnion faceBoundary allFaces hcount)
    hcover hzeroBase ?_ hstep horth
  intro e he
  rw [selectedBoundarySupport_eq_empty_of_totalIncidenceCount_eq_two_on_biUnion
    (faceBoundary := faceBoundary) (allFaces := allFaces) (S := allFaces) hcount] at he
  simp at he

end Mettapedia.GraphTheory.FourColor
