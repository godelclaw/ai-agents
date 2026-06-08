import Mettapedia.GraphTheory.FourColor.Theorem49AmbientSupport

namespace Mettapedia.GraphTheory.FourColor

variable {V F : Type*} [DecidableEq V] [DecidableEq F]

/-- A boundary-rooted face peel certificate for the Theorem 4.9 annihilator argument. The ordered
faces are peeled one by one; each face contributes a witness interior edge, and all remaining edges
of that face lie either on the selected ambient boundary support or among the witness edges of
earlier peeled faces. The only remaining geometric task in the proof route is to construct such a
certificate from the interior dual spanning forest of Lemma 4.6. -/
structure BoundaryRootedFacePeelCertificate {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) where
  faceOrder : List F
  witnessEdge : F → G.edgeSet
  coverInterior :
    interiorEdgeSupport faceBoundary allFaces ⊆
      facePeelWitnessSupport faceOrder witnessEdge
  step :
    ∀ l₁ l₂ f, faceOrder = l₁ ++ f :: l₂ →
      witnessEdge f ∈ faceBoundary f ∧
        (faceBoundary f).erase (witnessEdge f) ⊆
          selectedBoundarySupport faceBoundary allFaces allFaces ∪
            facePeelWitnessSupport l₁ witnessEdge

/-- Certificate-packaged form of the Theorem 4.9 annihilator step on the full ambient face-edge
support. Once a boundary-rooted face peel certificate is available, only the boundary-zero
hypothesis and orthogonality to the corresponding purified generators remain. -/
theorem zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (cert : BoundaryRootedFacePeelCertificate allFaces faceBoundary)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ cert.faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (cert.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_boundary_zero_and_facePeelWitnessCover
    (C := C) (htait := htait) (z := z)
    (baseZero := selectedBoundarySupport faceBoundary allFaces allFaces)
    (allFaces := allFaces) (faceBoundary := faceBoundary)
    (witnessEdge := cert.witnessEdge) (faceOrder := cert.faceOrder)
    hall cert.coverInterior hzeroBoundary hzeroBoundary cert.step horth

/-- Certificate-packaged Theorem 4.9 annihilator step with the local orthogonality hypotheses
lowered from the Definition 4.8 Kempe-closure generator family. This is the theorem-facing bridge
from the algebraic generator family to the existing boundary-rooted peeling certificate. -/
theorem zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (cert : BoundaryRootedFacePeelCertificate allFaces faceBoundary)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily faceBoundary C₀ z) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate
    (C := C) (htait := htait) (z := z)
    (allFaces := allFaces) (faceBoundary := faceBoundary) (cert := cert)
    (hall := hall) (hzeroBoundary := hzeroBoundary)
    (horth := by
      intro f _hf γ hγ0 hγne
      exact localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
        (faceBoundary := faceBoundary) (hC := hC) hgen
        (f := f) (e := cert.witnessEdge f) (htait (cert.witnessEdge f))
        γ hγ0 hγne)

/-- Closed-ambient certificate-packaged form of the Theorem 4.9 annihilator step. If every
ambient face-edge is incident to exactly two ambient faces, then a boundary-rooted face peel
certificate already forces vanishing on the full ambient support without any separate boundary-zero
hypothesis. -/
theorem zero_on_ambientFaceSupport_of_boundaryRootedFacePeelCertificate_of_totalIncidenceCount_eq_two
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (cert : BoundaryRootedFacePeelCertificate allFaces faceBoundary)
    (hcount : ∀ e ∈ allFaces.biUnion faceBoundary, totalIncidenceCount faceBoundary allFaces e = 2)
    (horth : ∀ f ∈ cert.faceOrder,
      ∀ γ, γ ≠ 0 → γ ≠ C (cert.witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (faceBoundary f))
            z
            (polarizedFaceGenerator C (C (cert.witnessEdge f)) (C (cert.witnessEdge f) + γ)
              (faceBoundary f)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  refine zero_on_ambientFaceSupport_of_totalIncidenceCount_eq_two_and_facePeelWitnessCover
    (C := C) (htait := htait) (z := z)
    (baseZero := selectedBoundarySupport faceBoundary allFaces allFaces)
    (allFaces := allFaces) (faceBoundary := faceBoundary)
    (witnessEdge := cert.witnessEdge) (faceOrder := cert.faceOrder)
    hcount cert.coverInterior ?_ ?_ horth
  · intro e he
    rw [selectedBoundarySupport_eq_empty_of_totalIncidenceCount_eq_two_on_biUnion
      (faceBoundary := faceBoundary) (allFaces := allFaces) (S := allFaces) hcount] at he
    simp at he
  · intro l₁ l₂ f hsplit
    rcases cert.step l₁ l₂ f hsplit with ⟨hwit, hsubset⟩
    refine ⟨hwit, ?_⟩
    intro e he
    rcases Finset.mem_union.1 (hsubset he) with hboundary | hprev
    · have hfalse : e ∈ (∅ : Finset G.edgeSet) := by
        rw [selectedBoundarySupport_eq_empty_of_totalIncidenceCount_eq_two_on_biUnion
          (faceBoundary := faceBoundary) (allFaces := allFaces) (S := allFaces) hcount] at hboundary
        exact hboundary
      simp at hfalse
    · exact Finset.mem_union.2 <| Or.inr hprev

end Mettapedia.GraphTheory.FourColor
