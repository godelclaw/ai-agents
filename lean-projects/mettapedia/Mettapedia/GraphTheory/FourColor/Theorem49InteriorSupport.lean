import Mettapedia.GraphTheory.FourColor.FaceIncidence
import Mettapedia.GraphTheory.FourColor.Theorem49FacePeeling

namespace Mettapedia.GraphTheory.FourColor

variable {V F : Type*} [DecidableEq V] [DecidableEq F]

/-- If the witness-edge support of a valid face peel order covers the ambient interior edge
support, then the Theorem 4.9 peeling argument already forces vanishing on every ambient interior
edge. This isolates the remaining geometric task to constructing the covering peel order from the
interior dual. -/
theorem zero_on_interiorEdgeSupport_of_facePeelWitnessCover {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (baseZero : Finset G.edgeSet) (allFaces : Finset F)
    (faceBoundary : F → Finset G.edgeSet) (witnessEdge : F → G.edgeSet) (faceOrder : List F)
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
    ∀ e ∈ interiorEdgeSupport faceBoundary allFaces, z e = 0 := by
  have hsupp :
      ∀ e ∈ facePeelWitnessSupport faceOrder witnessEdge, z e = 0 :=
    zero_on_facePeelWitnessSupport_from C htait z baseZero faceBoundary witnessEdge faceOrder
      hzeroBase hstep horth
  intro e he
  exact hsupp e (hcover he)

end Mettapedia.GraphTheory.FourColor
