import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- On any embedding with an unblocked interior endpoint, the full
selected-boundary-zero space strictly contains the concrete theorem-4.9 target
`W₀(H)` built from `selectedBoundaryInteriorEdgeEndpointVertices`: a single
interior edge gives a boundary-zero chain whose Kirchhoff sum is nonzero at
that surviving endpoint.  This is the precise algebraic reason the new
detector/cancellation oracle is stronger than the manuscript target on every
shell-bearing embedding. -/
theorem exists_mem_planarBoundaryZeroSubmodule_not_mem_theorem49BoundaryZeroKirchhoffSubspace_of_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ∉ theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb) := by
  classical
  rcases hEndpoint with ⟨e, heInterior, v, hvEdge, hAvoid⟩
  refine ⟨Pi.single e red, ?_, ?_⟩
  · intro e' he'
    by_cases hEq : e' = e
    · subst hEq
      exact False.elim
        ((Finset.disjoint_left.1
          (selectedBoundarySupport_disjoint_interiorEdgeSupport
            emb.faceBoundary emb.faces))
          he' heInterior)
    · simp [hEq]
  · intro hz
    have hvCarrier : v ∈ selectedBoundaryInteriorEdgeEndpointVertices emb := by
      exact (mem_selectedBoundaryInteriorEdgeEndpointVertices_iff emb).2
        ⟨⟨e, heInterior, hvEdge⟩, hAvoid⟩
    have hsumZero :
        vertexKirchhoffSum G (Pi.single e red) v = 0 :=
      kirchhoff_of_mem_theorem49BoundaryZeroKirchhoffSubspace hz v hvCarrier
    have hsumRed :
        vertexKirchhoffSum G (Pi.single e red) v = red := by
      unfold vertexKirchhoffSum incidentEdgeFinset
      simp [hvEdge]
    exact red_ne_zero (hsumRed.symm.trans hsumZero)

/-- For shell-bearing embeddings, the theorem-4.9 target `W₀(H)` is a proper
subspace of the full selected-boundary-zero chain space.  So any oracle stated
on all of `planarBoundaryZeroSubmodule` is formally stronger than the current
manuscript target. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_lt_planarBoundaryZeroSubmodule_of_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    (hEndpoint : HasUnblockedInteriorEndpoint emb) :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) <
      planarBoundaryZeroSubmodule emb := by
  refine lt_of_le_of_ne
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb))
    ?_
  intro hEq
  rcases
    exists_mem_planarBoundaryZeroSubmodule_not_mem_theorem49BoundaryZeroKirchhoffSubspace_of_hasUnblockedInteriorEndpoint
      hEndpoint with
    ⟨z, hzBoundary, hzNotTarget⟩
  exact hzNotTarget (by simpa [hEq] using hzBoundary)

end Mettapedia.GraphTheory.FourColor
