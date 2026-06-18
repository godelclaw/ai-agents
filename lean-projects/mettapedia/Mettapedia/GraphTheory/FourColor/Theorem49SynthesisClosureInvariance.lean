import Mettapedia.GraphTheory.FourColor.Theorem49Synthesis

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- The raw Definition 4.8 generator family depends only on the underlying edge-Kempe closure
class of the chosen base coloring. -/
theorem kempeClosureGeneratorFamily_eq_of_edgeKempeClosure_eq
    {G : SimpleGraph V} {F : Type*} {faceBoundary : F → Finset G.edgeSet}
    {C₀ C₁ : G.EdgeColoring Color}
    (hclosure : G.EdgeKempeClosure C₀ = G.EdgeKempeClosure C₁) :
    kempeClosureGeneratorFamily faceBoundary C₀ =
      kempeClosureGeneratorFamily faceBoundary C₁ := by
  ext x
  simp [kempeClosureGeneratorFamily, hclosure]

/-- The raw Definition 4.8 generator span depends only on the underlying edge-Kempe closure
class of the chosen base coloring. -/
theorem kempeClosureGeneratorSubspace_eq_of_edgeKempeClosure_eq
    {G : SimpleGraph V} {F : Type*} {faceBoundary : F → Finset G.edgeSet}
    {C₀ C₁ : G.EdgeColoring Color}
    (hclosure : G.EdgeKempeClosure C₀ = G.EdgeKempeClosure C₁) :
    kempeClosureGeneratorSubspace faceBoundary C₀ =
      kempeClosureGeneratorSubspace faceBoundary C₁ := by
  simp [kempeClosureGeneratorSubspace,
    kempeClosureGeneratorFamily_eq_of_edgeKempeClosure_eq hclosure]

/-- The selected-boundary-projected Definition 4.8 generator family depends only on the
underlying edge-Kempe closure class of the chosen base coloring. -/
theorem projectedKempeClosureGeneratorFamily_eq_of_edgeKempeClosure_eq
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {C₀ C₁ : G.EdgeColoring Color}
    (hclosure : G.EdgeKempeClosure C₀ = G.EdgeKempeClosure C₁) :
    projectedKempeClosureGeneratorFamily emb C₀ =
      projectedKempeClosureGeneratorFamily emb C₁ := by
  simp [projectedKempeClosureGeneratorFamily,
    kempeClosureGeneratorFamily_eq_of_edgeKempeClosure_eq hclosure]

/-- The selected-boundary-projected Definition 4.8 generator span depends only on the
underlying edge-Kempe closure class of the chosen base coloring. -/
theorem projectedKempeClosureGeneratorSubspace_eq_of_edgeKempeClosure_eq
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {C₀ C₁ : G.EdgeColoring Color}
    (hclosure : G.EdgeKempeClosure C₀ = G.EdgeKempeClosure C₁) :
    projectedKempeClosureGeneratorSubspace emb C₀ =
      projectedKempeClosureGeneratorSubspace emb C₁ := by
  simp [projectedKempeClosureGeneratorSubspace,
    kempeClosureGeneratorSubspace_eq_of_edgeKempeClosure_eq hclosure]

/-- The route-level Theorem 4.9 synthesis package is invariant under replacing the base Tait
coloring by another one with the same edge-Kempe closure class. -/
theorem Theorem49BoundaryRootSynthesis.of_edgeKempeClosure_eq
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ C₁ : G.EdgeColoring Color}
    (hclosure : G.EdgeKempeClosure C₀ = G.EdgeKempeClosure C₁)
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Theorem49BoundaryRootSynthesis emb C₁ := by
  have hrawFamily :
      kempeClosureGeneratorFamily emb.faceBoundary C₀ =
        kempeClosureGeneratorFamily emb.faceBoundary C₁ :=
    kempeClosureGeneratorFamily_eq_of_edgeKempeClosure_eq hclosure
  have hrawSubspace :
      kempeClosureGeneratorSubspace emb.faceBoundary C₀ =
        kempeClosureGeneratorSubspace emb.faceBoundary C₁ :=
    kempeClosureGeneratorSubspace_eq_of_edgeKempeClosure_eq hclosure
  have hprojFamily :
      projectedKempeClosureGeneratorFamily emb C₀ =
        projectedKempeClosureGeneratorFamily emb C₁ :=
    projectedKempeClosureGeneratorFamily_eq_of_edgeKempeClosure_eq hclosure
  have hprojSubspace :
      projectedKempeClosureGeneratorSubspace emb C₀ =
        projectedKempeClosureGeneratorSubspace emb C₁ :=
    projectedKempeClosureGeneratorSubspace_eq_of_edgeKempeClosure_eq hclosure
  have hpointwise :
      ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb),
        (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₁,
          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
    intro z
    simpa [hprojSubspace] using h.pointwise_separation z
  have hpairingKer :
      LinearMap.ker
          (theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
            (G := G) emb C₁ (selectedBoundaryInteriorEdgeEndpointVertices emb)) =
        ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    exact (hpointwise z).1 (by
      intro p hp
      let p' : projectedKempeClosureGeneratorSubspace emb C₁ := ⟨p, hp⟩
      have hcoord := congrArg
        (fun f : projectedKempeClosureGeneratorSubspace emb C₁ →ₗ[F2] F2 => f p') hz
      simpa [theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap, p'] using hcoord)
  have hfinrank :
      Module.finrank F2
          (theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) ≤
        Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₁) := by
    let L :=
      theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
        (G := G) emb C₁ (selectedBoundaryInteriorEdgeEndpointVertices emb)
    have hinj : Function.Injective L := (LinearMap.ker_eq_bot).1 hpairingKer
    have hleDual :
        Module.finrank F2
            (theorem49BoundaryZeroKirchhoffSubspace emb
              (selectedBoundaryInteriorEdgeEndpointVertices emb)) ≤
          Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₁ →ₗ[F2] F2) :=
      LinearMap.finrank_le_finrank_of_injective (f := L) hinj
    simpa [L, Module.Dual] using
      hleDual.trans_eq
        (Subspace.dual_finrank_eq
          (K := F2) (V := projectedKempeClosureGeneratorSubspace emb C₁))
  refine
    { target_eq_boundaryProjectionImage := h.target_eq_boundaryProjectionImage
      pointwise_separation := by
        exact hpointwise
      pairing_ker_eq_bot := by
        exact hpairingKer
      finrank_le_projectedGeneratorSubspace := by
        exact hfinrank
      target_eq_projectedGeneratorSource := by
        simpa [hprojSubspace] using h.target_eq_projectedGeneratorSource
      target_le_projectedGeneratorSubspace := by
        simpa [hprojSubspace] using h.target_le_projectedGeneratorSubspace
      target_le_projectedGeneratorFamilySpan := by
        simpa [hprojFamily] using h.target_le_projectedGeneratorFamilySpan
      target_eq_rawSourceImage := by
        simpa [hrawSubspace] using h.target_eq_rawSourceImage
      projectedGeneratorRepresentation := by
        intro z hz
        simpa [hprojFamily] using h.projectedGeneratorRepresentation hz
      rawGeneratorProjectionRepresentation := by
        intro z hz
        simpa [hrawFamily] using h.rawGeneratorProjectionRepresentation hz
      rawSourcePreimage := by
        intro z hz
        simpa [hrawSubspace] using h.rawSourcePreimage hz
      rawKirchhoffRepresentative := by
        intro x hx
        simpa [hrawFamily] using h.rawKirchhoffRepresentative hx
      rawBoundaryKernelDecomposition := by
        intro x hx
        simpa [hrawFamily] using h.rawBoundaryKernelDecomposition hx }

/-- Mutual edge-Kempe reachability is enough to transport the route-level Theorem 4.9 synthesis
package between base Tait colorings. -/
theorem Theorem49BoundaryRootSynthesis.of_mutual_edgeKempeReachability
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ C₁ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (h₀₁ : C₁ ∈ G.EdgeKempeClosure C₀) (h₁₀ : C₀ ∈ G.EdgeKempeClosure C₁) :
    Theorem49BoundaryRootSynthesis emb C₁ :=
  Theorem49BoundaryRootSynthesis.of_edgeKempeClosure_eq
    (G := G) (emb := emb)
    (G.edgeKempeClosure_eq_of_mem_of_mem h₀₁ h₁₀) h

end Mettapedia.GraphTheory.FourColor
