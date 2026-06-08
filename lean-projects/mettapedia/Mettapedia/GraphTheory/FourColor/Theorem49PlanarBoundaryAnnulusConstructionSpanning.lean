import Mettapedia.GraphTheory.FourColor.Theorem49BoundaryProjection
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusConstructionCore

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The annulus-construction route with the explicit parent-witness orientation hypothesis already
reaches the fixed-embedding Theorem 4.9 annihilator endpoint. This packages the existing
well-founded peeling theorem in the `BoundaryZeroAnnihilatorTrivialForEmbedding` form used by the
algebraic spanning bridge. -/
theorem
    zero_on_allEdges_of_planarBoundaryAnnulusConstruction_of_parentWitness_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    (C₀ C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C)
    (hC : C ∈ G.EdgeKempeClosure C₀) (z : G.edgeSet → Color)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (hgen : AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    ∀ e, z e = 0 := by
  exact
    zero_on_allEdges_of_boundary_zero_and_planarBoundaryAttachedRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
      (data := (data.toPlanarBoundaryWellFoundedFacePeelWitnessData_of_parentWitness
        hparentWitness).toPlanarBoundaryAttachedRootedFacePeelCertificate)
      (C₀ := C₀) (C := C) (htait := htait) (hC := hC) (z := z)
      (hzeroBoundary := hzeroBoundary) (hgen := hgen)

/-- The explicit parent-witness orientation surface on annulus-construction data is already
strong enough to discharge the non-geometric Theorem 4.9 bridge hypothesis: every boundary-zero
annihilator of the Definition 4.8 family is zero. -/
theorem boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryAnnulusConstruction_of_parentWitness
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀ := by
  intro z hzeroBoundary hgen e
  exact
    zero_on_allEdges_of_planarBoundaryAnnulusConstruction_of_parentWitness_of_annihilatesKempeClosureGeneratorFamily
      emb data hparentWitness C₀ C₀ hC₀ (G.mem_edgeKempeClosure_self C₀) z
      hzeroBoundary hgen e

/-- The annulus-construction route therefore already yields the corrected v23 span identity on
the selected-boundary-erased Definition 4.8 generator subspace. -/
theorem projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryAnnulusConstruction_of_parentWitness
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    projectedKempeClosureGeneratorSubspace emb C₀ = planarBoundaryZeroSubmodule emb :=
  projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryAnnulusConstruction_of_parentWitness
      emb data hparentWitness C₀ hC₀)

/-- Explicit-family form of the same annulus-construction span identity. -/
theorem span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryAnnulusConstruction_of_parentWitness
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
      planarBoundaryZeroSubmodule emb := by
  rw [← projectedKempeClosureGeneratorSubspace_eq_span_projectedKempeClosureGeneratorFamily]
  exact
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryAnnulusConstruction_of_parentWitness
      emb data hparentWitness C₀ hC₀

/-- Pointwise `W₀(H)` separation for the purified endpoint carrier, obtained directly from the
annulus-construction parent-witness route via the generic annihilator bridge. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryAnnulusConstruction_of_parentWitness
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    {C₀ : G.EdgeColoring Color} (hC₀ : IsTaitEdgeColoring G C₀)
    {z : theorem49BoundaryZeroKirchhoffSubspace emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb)} :
    (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
      z = 0 := by
  constructor
  · intro hzero
    have hboundaryZero :
        ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
          (z : G.edgeSet → Color) e = 0 :=
      boundaryZero_of_mem_theorem49BoundaryZeroKirchhoffSubspace z.property
    have horth :
        ((z : theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
          G.edgeSet → Color) ∈
          (chainDotBilinForm G.edgeSet).orthogonal
            (projectedKempeClosureGeneratorSubspace emb C₀) := by
      intro p hp
      exact hzero p hp
    have hgen :
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀
          ((z : theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
            G.edgeSet → Color) :=
      (mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_iff_annihilatesKempeClosureGeneratorFamily
        (G := G) (emb := emb) (C₀ := C₀)
        (z := ((z : theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
          G.edgeSet → Color))
        (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
          emb (selectedBoundaryInteriorEdgeEndpointVertices emb) z.property)).1 horth
    apply Subtype.ext
    funext e
    exact
      boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryAnnulusConstruction_of_parentWitness
        emb data hparentWitness C₀ hC₀
        ((z : theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
          G.edgeSet → Color)
        hboundaryZero hgen e
  · intro hz p _hp
    rw [hz]
    exact (chainDotBilinForm G.edgeSet p).map_zero

/-- Kernel form of the same separation theorem on the purified endpoint carrier. -/
theorem ker_theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap_eq_bot_of_planarBoundaryAnnulusConstruction_of_parentWitness
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    {C₀ : G.EdgeColoring Color} (hC₀ : IsTaitEdgeColoring G C₀) :
    LinearMap.ker
        (theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
          (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb)) =
      ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  exact
    (theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorEdgeEndpointVertices_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryAnnulusConstruction_of_parentWitness
      (G := G) (emb := emb) data hparentWitness hC₀ (z := z)).1
      (by
        intro p hp
        let p' : projectedKempeClosureGeneratorSubspace emb C₀ := ⟨p, hp⟩
        have hmap :
            theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
                (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb) z = 0 := hz
        have hcoord := congrArg
          (fun f : projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2 => f p') hmap
        simpa [theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap, p'] using
          hcoord)

/-- Finite-dimensional consequence of the annulus-construction parent-witness route: the purified
`W₀(H)` target has dimension at most the projected Definition 4.8 generator span. -/
theorem finrank_theorem49BoundaryZeroKirchhoffSubspace_le_finrank_projectedKempeClosureGeneratorSubspace_of_planarBoundaryAnnulusConstruction_of_parentWitness
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    {C₀ : G.EdgeColoring Color} (hC₀ : IsTaitEdgeColoring G C₀) :
    Module.finrank F2
        (theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb)) ≤
      Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀) := by
  let L :=
    theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
      (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb)
  have hker :
      LinearMap.ker L = ⊥ :=
    ker_theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap_eq_bot_of_planarBoundaryAnnulusConstruction_of_parentWitness
      (G := G) (emb := emb) data hparentWitness hC₀
  have hinj : Function.Injective L := (LinearMap.ker_eq_bot).1 hker
  have hleDual :
      Module.finrank F2
          (theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) ≤
        Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2) :=
    LinearMap.finrank_le_finrank_of_injective (f := L) hinj
  simpa [L, Module.Dual] using
    hleDual.trans_eq
      (Subspace.dual_finrank_eq
        (K := F2) (V := projectedKempeClosureGeneratorSubspace emb C₀))

/-- Route-facing Theorem 4.9 characterization obtained directly from annulus-construction parent
witness orientation, without passing through the older interior-dual boundary-root wrappers. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_planarBoundaryAnnulusConstruction_of_parentWitness
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices =
      kirchhoffSubmodule G vertices ⊓ projectedKempeClosureGeneratorSubspace emb C₀ := by
  rw [theorem49BoundaryZeroKirchhoffSubspace,
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryAnnulusConstruction_of_parentWitness
      emb data hparentWitness C₀ hC₀]

/-- Inclusion form of the same direct annulus-construction algebraic bridge. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_planarBoundaryAnnulusConstruction_of_parentWitness
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ≤
      projectedKempeClosureGeneratorSubspace emb C₀ :=
  theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryAnnulusConstruction_of_parentWitness
      emb data hparentWitness C₀ hC₀)
    vertices

/-- Raw-source preimage form of the corrected Theorem 4.9 source, reached directly from the
annulus-construction parent-witness route through the generic annihilator bridge. -/
theorem exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryAnnulusConstruction_of_parentWitness
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀,
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z :=
  exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryAnnulusConstruction_of_parentWitness
      emb data hparentWitness C₀ hC₀)
    vertices hz

end Mettapedia.GraphTheory.FourColor
