import Mettapedia.GraphTheory.FourColor.Theorem49LinearAlgebra
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryInteriorDual

namespace Mettapedia.GraphTheory.FourColor

open LinearMap

variable {V : Type*} [DecidableEq V]

/-- The annihilator endpoint already supplied by the Theorem 4.9 peeling route on a fixed
embedding: every boundary-zero chain annihilating the Definition 4.8 Kempe-closure generator
family is zero on all edges. -/
def BoundaryZeroAnnihilatorTrivialForEmbedding {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (C0 : G.EdgeColoring Color) : Prop :=
  ∀ z : G.edgeSet → Color,
    (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) →
    AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z →
    ∀ e, z e = 0

/-- The algebraic Theorem 4.9 bridge not yet supplied by the certificate route.  It names the
actual boundary-compatible difference space, the span of the available Kempe-closure generators,
and the linear-duality step turning trivial annihilator into spanning.

This is intentionally not another certificate or annulus-construction wrapper: it is the missing
non-geometric interface between the proved annihilator endpoint and the v23 spanning statement. -/
structure Theorem49LinearDualityBridge {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (C0 : G.EdgeColoring Color) where
  differenceSpace : Set (G.edgeSet → Color)
  generatorSpan : Set (G.edgeSet → Color)
  generatorSpan_subset_differenceSpace : generatorSpan ⊆ differenceSpace
  differenceSpace_subset_generatorSpan_of_boundaryZeroAnnihilatorTrivial :
    BoundaryZeroAnnihilatorTrivialForEmbedding emb C0 → differenceSpace ⊆ generatorSpan

theorem Theorem49LinearDualityBridge.generatorSpan_eq_differenceSpace {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {C0 : G.EdgeColoring Color}
    (bridge : Theorem49LinearDualityBridge emb C0)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C0) :
    bridge.generatorSpan = bridge.differenceSpace := by
  ext x
  constructor
  · intro hx
    exact bridge.generatorSpan_subset_differenceSpace hx
  · intro hx
    exact bridge.differenceSpace_subset_generatorSpan_of_boundaryZeroAnnihilatorTrivial
      htrivial hx

/-- Concrete submodule version of the remaining Theorem 4.9 algebraic interface.  It replaces
the set-level span bridge by actual `𝔽₂`-subspaces, a bilinear form, and the two identification
fields needed to apply the already-proved annihilator endpoint:

* membership in the target subspace gives boundary vanishing;
* membership in the orthogonal complement of the generator subspace gives annihilation of the
  Definition 4.8 Kempe-closure generator family. -/
structure Theorem49SubmoduleDualityData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (C0 : G.EdgeColoring Color) where
  differenceSubspace : Submodule F2 (G.edgeSet → Color)
  generatorSubspace : Submodule F2 (G.edgeSet → Color)
  bilinearForm : LinearMap.BilinForm F2 (G.edgeSet → Color)
  bilinearForm_nondegenerate : bilinearForm.Nondegenerate
  bilinearForm_isRefl : bilinearForm.IsRefl
  generatorSubspace_le_differenceSubspace : generatorSubspace ≤ differenceSubspace
  boundaryZero_of_mem_differenceSubspace :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ differenceSubspace →
        ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0
  annihilatesGeneratorFamily_of_mem_orthogonal :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ bilinearForm.orthogonal generatorSubspace →
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z

theorem Theorem49SubmoduleDualityData.inf_orthogonal_eq_bot_of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C0 : G.EdgeColoring Color}
    (data : Theorem49SubmoduleDualityData emb C0)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C0) :
    data.differenceSubspace ⊓ data.bilinearForm.orthogonal data.generatorSubspace = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  exact funext
    (htrivial z
      (data.boundaryZero_of_mem_differenceSubspace hz.1)
      (data.annihilatesGeneratorFamily_of_mem_orthogonal hz.2))

theorem Theorem49SubmoduleDualityData.generatorSubspace_eq_differenceSubspace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C0 : G.EdgeColoring Color}
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (data : Theorem49SubmoduleDualityData emb C0)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C0) :
    data.generatorSubspace = data.differenceSubspace :=
  submodule_eq_of_le_of_inf_orthogonal_eq_bot
    data.bilinearForm data.bilinearForm_nondegenerate data.bilinearForm_isRefl
    data.generatorSubspace_le_differenceSubspace
    (data.inf_orthogonal_eq_bot_of_boundaryZeroAnnihilatorTrivial htrivial)

/-- Relative version of the concrete Theorem 4.9 submodule bridge.  The orthogonality-to-
annihilator field may use the fact that the tested chain belongs to the target difference
subspace.  This is needed for boundary-erased generator sources: orthogonality to the projected
span only recovers raw generator annihilation for chains already known to vanish on the selected
boundary. -/
structure Theorem49RelativeSubmoduleDualityData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) (C0 : G.EdgeColoring Color) where
  differenceSubspace : Submodule F2 (G.edgeSet → Color)
  generatorSubspace : Submodule F2 (G.edgeSet → Color)
  bilinearForm : LinearMap.BilinForm F2 (G.edgeSet → Color)
  bilinearForm_nondegenerate : bilinearForm.Nondegenerate
  bilinearForm_isRefl : bilinearForm.IsRefl
  generatorSubspace_le_differenceSubspace : generatorSubspace ≤ differenceSubspace
  boundaryZero_of_mem_differenceSubspace :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ differenceSubspace →
        ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0
  annihilatesGeneratorFamily_of_mem_differenceSubspace_of_mem_orthogonal :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ differenceSubspace →
      z ∈ bilinearForm.orthogonal generatorSubspace →
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z

theorem Theorem49RelativeSubmoduleDualityData.inf_orthogonal_eq_bot_of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C0 : G.EdgeColoring Color}
    (data : Theorem49RelativeSubmoduleDualityData emb C0)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C0) :
    data.differenceSubspace ⊓ data.bilinearForm.orthogonal data.generatorSubspace = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  exact funext
    (htrivial z
      (data.boundaryZero_of_mem_differenceSubspace hz.1)
      (data.annihilatesGeneratorFamily_of_mem_differenceSubspace_of_mem_orthogonal hz.1 hz.2))

theorem Theorem49RelativeSubmoduleDualityData.generatorSubspace_eq_differenceSubspace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C0 : G.EdgeColoring Color}
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (data : Theorem49RelativeSubmoduleDualityData emb C0)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C0) :
    data.generatorSubspace = data.differenceSubspace :=
  submodule_eq_of_le_of_inf_orthogonal_eq_bot
    data.bilinearForm data.bilinearForm_nondegenerate data.bilinearForm_isRefl
    data.generatorSubspace_le_differenceSubspace
    (data.inf_orthogonal_eq_bot_of_boundaryZeroAnnihilatorTrivial htrivial)

/-- The older non-relative interface is a special case of the relative bridge. -/
def Theorem49RelativeSubmoduleDualityData.ofSubmoduleDualityData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C0 : G.EdgeColoring Color}
    (data : Theorem49SubmoduleDualityData emb C0) :
    Theorem49RelativeSubmoduleDualityData emb C0 where
  differenceSubspace := data.differenceSubspace
  generatorSubspace := data.generatorSubspace
  bilinearForm := data.bilinearForm
  bilinearForm_nondegenerate := data.bilinearForm_nondegenerate
  bilinearForm_isRefl := data.bilinearForm_isRefl
  generatorSubspace_le_differenceSubspace := data.generatorSubspace_le_differenceSubspace
  boundaryZero_of_mem_differenceSubspace := data.boundaryZero_of_mem_differenceSubspace
  annihilatesGeneratorFamily_of_mem_differenceSubspace_of_mem_orthogonal := by
    intro z _hzDiff hzOrth
    exact data.annihilatesGeneratorFamily_of_mem_orthogonal hzOrth

/-- A concrete submodule/bilinear-form data package instantiates the earlier set-level bridge. -/
def Theorem49LinearDualityBridge.ofSubmoduleDualityData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C0 : G.EdgeColoring Color}
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (data : Theorem49SubmoduleDualityData emb C0) :
    Theorem49LinearDualityBridge emb C0 where
  differenceSpace := data.differenceSubspace
  generatorSpan := data.generatorSubspace
  generatorSpan_subset_differenceSpace := data.generatorSubspace_le_differenceSubspace
  differenceSpace_subset_generatorSpan_of_boundaryZeroAnnihilatorTrivial := by
    intro htrivial x hx
    rw [data.generatorSubspace_eq_differenceSubspace htrivial]
    exact hx

/-- A relative submodule/bilinear-form data package also instantiates the set-level bridge. -/
def Theorem49LinearDualityBridge.ofRelativeSubmoduleDualityData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C0 : G.EdgeColoring Color}
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (data : Theorem49RelativeSubmoduleDualityData emb C0) :
    Theorem49LinearDualityBridge emb C0 where
  differenceSpace := data.differenceSubspace
  generatorSpan := data.generatorSubspace
  generatorSpan_subset_differenceSpace := data.generatorSubspace_le_differenceSubspace
  differenceSpace_subset_generatorSpan_of_boundaryZeroAnnihilatorTrivial := by
    intro htrivial x hx
    rw [data.generatorSubspace_eq_differenceSubspace htrivial]
    exact hx

/-- The standard finite chain dot product fills the bilinear-form part of the concrete algebraic
bridge.  After this constructor, the only remaining algebraic fields are the actual definitions of
the v23 target and generator subspaces, plus the two identification lemmas connecting them to
boundary vanishing and Definition 4.8 generator-family annihilation. -/
noncomputable def Theorem49SubmoduleDualityData.ofChainDot
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C0 : G.EdgeColoring Color}
    [Fintype G.edgeSet]
    (differenceSubspace generatorSubspace : Submodule F2 (G.edgeSet → Color))
    (hle : generatorSubspace ≤ differenceSubspace)
    (hboundary :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ differenceSubspace →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ (chainDotBilinForm G.edgeSet).orthogonal generatorSubspace →
          AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z) :
    Theorem49SubmoduleDualityData emb C0 where
  differenceSubspace := differenceSubspace
  generatorSubspace := generatorSubspace
  bilinearForm := chainDotBilinForm G.edgeSet
  bilinearForm_nondegenerate := chainDotBilinForm_nondegenerate G.edgeSet
  bilinearForm_isRefl := chainDotBilinForm_isRefl G.edgeSet
  generatorSubspace_le_differenceSubspace := hle
  boundaryZero_of_mem_differenceSubspace := hboundary
  annihilatesGeneratorFamily_of_mem_orthogonal := horth

/-- Standard-chain-dot constructor for the relative submodule bridge.  The only difference from
`ofChainDot` is that the generator-family annihilation proof is allowed to use target-subspace
membership. -/
noncomputable def Theorem49RelativeSubmoduleDualityData.ofChainDot
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C0 : G.EdgeColoring Color}
    [Fintype G.edgeSet]
    (differenceSubspace generatorSubspace : Submodule F2 (G.edgeSet → Color))
    (hle : generatorSubspace ≤ differenceSubspace)
    (hboundary :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ differenceSubspace →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ differenceSubspace →
        z ∈ (chainDotBilinForm G.edgeSet).orthogonal generatorSubspace →
          AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z) :
    Theorem49RelativeSubmoduleDualityData emb C0 where
  differenceSubspace := differenceSubspace
  generatorSubspace := generatorSubspace
  bilinearForm := chainDotBilinForm G.edgeSet
  bilinearForm_nondegenerate := chainDotBilinForm_nondegenerate G.edgeSet
  bilinearForm_isRefl := chainDotBilinForm_isRefl G.edgeSet
  generatorSubspace_le_differenceSubspace := hle
  boundaryZero_of_mem_differenceSubspace := hboundary
  annihilatesGeneratorFamily_of_mem_differenceSubspace_of_mem_orthogonal := horth

/-- The boundary-rooted interior-dual data now reaches the precise non-certificate endpoint needed
for the algebraic spanning bridge: triviality of all boundary-zero annihilators. -/
theorem boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    BoundaryZeroAnnihilatorTrivialForEmbedding emb C0 := by
  intro z hzeroBoundary hgen e
  exact
    zero_on_allEdges_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_annihilatesKempeClosureGeneratorFamily
      emb C0 C0 hC0 (G.mem_edgeKempeClosure_self C0) z data hzeroBoundary hgen e

/-- A same-embedding height-ordered witness-cover package supplies the annihilator endpoint needed
by the concrete submodule-duality spanning bridge. -/
theorem boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    BoundaryZeroAnnihilatorTrivialForEmbedding emb C0 := by
  intro z hzeroBoundary hgen e
  exact
    zero_on_allEdges_of_planarBoundaryHeightOrderedFacePeelWitnessData
      (emb := emb) (C := C0) (htait := hC0) (z := z) (data := data)
      (hzeroBoundary := hzeroBoundary) (horth := by
        intro f _hf γ hγ0 hγne
        simpa using
          localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
            (faceBoundary := emb.faceBoundary) (hC := G.mem_edgeKempeClosure_self C0) hgen
            (f := f.1) (e := data.witnessEdge f) (hC0 (data.witnessEdge f))
            γ hγ0 hγne)
      e

/-- A same-embedding finite collar-layer witness-cover package supplies the annihilator endpoint
needed by the concrete submodule-duality spanning bridge. -/
theorem boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    BoundaryZeroAnnihilatorTrivialForEmbedding emb C0 := by
  intro z hzeroBoundary hgen e
  exact
    zero_on_allEdges_of_planarBoundaryCollarLayerFacePeelWitnessData
      (emb := emb) (C := C0) (htait := hC0) (z := z) (data := data)
      (hzeroBoundary := hzeroBoundary) (horth := by
        intro _i f _hf γ hγ0 hγne
        simpa using
          localOrthogonality_of_annihilatesKempeClosureGeneratorFamily
            (faceBoundary := emb.faceBoundary) (hC := G.mem_edgeKempeClosure_self C0) hgen
            (f := f.1) (e := data.witnessEdge f) (hC0 (data.witnessEdge f))
            γ hγ0 hγne)
      e

/-- The weaker local explicit-remainder collar package also supplies the annihilator endpoint
needed by the concrete submodule-duality spanning bridge. -/
theorem boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0) :
    BoundaryZeroAnnihilatorTrivialForEmbedding emb C0 := by
  intro z hzeroBoundary hgen e
  exact
    zero_on_allEdges_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData_of_annihilatesKempeClosureGeneratorFamily
      (emb := emb) (C₀ := C0) (C := C0) (htait := hC0)
      (hC := G.mem_edgeKempeClosure_self C0) (z := z) (data := data)
      (hzeroBoundary := hzeroBoundary) (hgen := hgen) e

/-- Certificate-complete geometry plus the explicit linear-duality bridge gives the v23 Theorem
4.9-style span equality on the bridge's two named spaces. -/
theorem theorem49_spanning_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_and_linearDualityBridge
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (bridge : Theorem49LinearDualityBridge emb C0) :
    bridge.generatorSpan = bridge.differenceSpace :=
  bridge.generatorSpan_eq_differenceSpace
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C0 hC0)

/-- Same theorem as the set-level bridge, but with the remaining algebra supplied as concrete
subspaces and a nondegenerate reflexive bilinear form. -/
theorem theorem49_submodule_spanning_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (algebra : Theorem49SubmoduleDualityData emb C0) :
    algebra.generatorSubspace = algebra.differenceSubspace :=
  algebra.generatorSubspace_eq_differenceSubspace
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C0 hC0)

/-- Same spanning theorem for the relative submodule bridge, where orthogonality may be interpreted
relative to membership in the target difference subspace. -/
theorem theorem49_relative_submodule_spanning_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (algebra : Theorem49RelativeSubmoduleDualityData emb C0) :
    algebra.generatorSubspace = algebra.differenceSubspace :=
  algebra.generatorSubspace_eq_differenceSubspace
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C0 hC0)

/-- Theorem 4.9 spanning conclusion with the standard finite chain dot product already installed.
The remaining inputs are exactly the concrete v23 subspaces and the two identification lemmas:
membership in the target subspace gives boundary-zero chains, and orthogonality to the generator
span is the Definition 4.8 generator-family annihilation condition. -/
theorem theorem49_chainDot_spanning_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (differenceSubspace generatorSubspace : Submodule F2 (G.edgeSet → Color))
    (hle : generatorSubspace ≤ differenceSubspace)
    (hboundary :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ differenceSubspace →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ (chainDotBilinForm G.edgeSet).orthogonal generatorSubspace →
          AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z) :
    generatorSubspace = differenceSubspace :=
  theorem49_submodule_spanning_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    emb data C0 hC0
    (Theorem49SubmoduleDualityData.ofChainDot
      differenceSubspace generatorSubspace hle hboundary horth)

/-- Same submodule-duality spanning theorem with the annihilator endpoint supplied directly by a
same-embedding height-ordered witness-cover package. -/
theorem theorem49_submodule_spanning_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (algebra : Theorem49SubmoduleDualityData emb C0) :
    algebra.generatorSubspace = algebra.differenceSubspace :=
  algebra.generatorSubspace_eq_differenceSubspace
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C0 hC0)

/-- Chain-dot specialization of the height-ordered witness-cover spanning bridge.  This is the
version that constructs the concrete `Theorem49SubmoduleDualityData` package from the named
subspaces and their two identification lemmas. -/
theorem theorem49_chainDot_spanning_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (differenceSubspace generatorSubspace : Submodule F2 (G.edgeSet → Color))
    (hle : generatorSubspace ≤ differenceSubspace)
    (hboundary :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ differenceSubspace →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ (chainDotBilinForm G.edgeSet).orthogonal generatorSubspace →
          AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z) :
    generatorSubspace = differenceSubspace :=
  theorem49_submodule_spanning_of_planarBoundaryHeightOrderedFacePeelWitnessData
    emb data C0 hC0
    (Theorem49SubmoduleDualityData.ofChainDot
      differenceSubspace generatorSubspace hle hboundary horth)

/-- Same submodule-duality spanning theorem with the annihilator endpoint supplied directly by a
same-embedding finite collar-layer witness-cover package. -/
theorem theorem49_submodule_spanning_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (algebra : Theorem49SubmoduleDualityData emb C0) :
    algebra.generatorSubspace = algebra.differenceSubspace :=
  algebra.generatorSubspace_eq_differenceSubspace
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C0 hC0)

/-- Chain-dot specialization of the finite collar-layer witness-cover spanning bridge.  This is the
paper-facing finite-collar version of the submodule-duality spanning gap. -/
theorem theorem49_chainDot_spanning_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (differenceSubspace generatorSubspace : Submodule F2 (G.edgeSet → Color))
    (hle : generatorSubspace ≤ differenceSubspace)
    (hboundary :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ differenceSubspace →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ (chainDotBilinForm G.edgeSet).orthogonal generatorSubspace →
          AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z) :
    generatorSubspace = differenceSubspace :=
  theorem49_submodule_spanning_of_planarBoundaryCollarLayerFacePeelWitnessData
    emb data C0 hC0
    (Theorem49SubmoduleDualityData.ofChainDot
      differenceSubspace generatorSubspace hle hboundary horth)

/-- Chain-dot specialization of the relative submodule spanning theorem. -/
theorem theorem49_chainDot_relative_spanning_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (differenceSubspace generatorSubspace : Submodule F2 (G.edgeSet → Color))
    (hle : generatorSubspace ≤ differenceSubspace)
    (hboundary :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ differenceSubspace →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ differenceSubspace →
        z ∈ (chainDotBilinForm G.edgeSet).orthogonal generatorSubspace →
          AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z) :
    generatorSubspace = differenceSubspace :=
  theorem49_relative_submodule_spanning_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    emb data C0 hC0
    (Theorem49RelativeSubmoduleDualityData.ofChainDot
      differenceSubspace generatorSubspace hle hboundary horth)

/-- Graph-level gap map for the annulus route: once an embedding with boundary-rooted interior-dual
data is available, the only extra field needed here is a same-embedding linear-duality bridge from
the annihilator endpoint to actual spanning. -/
theorem exists_theorem49_spanning_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_and_linearDualityBridge
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (bridgeOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb →
        Theorem49LinearDualityBridge emb C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        (bridgeOf emb data).generatorSpan = (bridgeOf emb data).differenceSpace := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49_spanning_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_and_linearDualityBridge
      emb data C0 hC0 (bridgeOf emb data)⟩

/-- Graph-level version of the relative submodule bridge.  This is the form needed by corrected
projected-source instantiations, where orthogonality-to-annihilator uses target membership. -/
theorem exists_theorem49_relative_submodule_spanning_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (algebraOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb →
        Theorem49RelativeSubmoduleDualityData emb C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        (algebraOf emb data).generatorSubspace = (algebraOf emb data).differenceSubspace := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49_relative_submodule_spanning_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C0 hC0 (algebraOf emb data)⟩

/-- Same spanning theorem for the relative submodule bridge, with the annihilator endpoint supplied
by a same-embedding height-ordered witness-cover package. -/
theorem theorem49_relative_submodule_spanning_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (algebra : Theorem49RelativeSubmoduleDualityData emb C0) :
    algebra.generatorSubspace = algebra.differenceSubspace :=
  algebra.generatorSubspace_eq_differenceSubspace
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C0 hC0)

/-- Same spanning theorem for the relative submodule bridge, with the annihilator endpoint supplied
by a same-embedding finite collar-layer witness-cover package. -/
theorem theorem49_relative_submodule_spanning_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (algebra : Theorem49RelativeSubmoduleDualityData emb C0) :
    algebra.generatorSubspace = algebra.differenceSubspace :=
  algebra.generatorSubspace_eq_differenceSubspace
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C0 hC0)

/-- Chain-dot specialization of the relative height-ordered submodule spanning theorem. -/
theorem theorem49_chainDot_relative_spanning_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (differenceSubspace generatorSubspace : Submodule F2 (G.edgeSet → Color))
    (hle : generatorSubspace ≤ differenceSubspace)
    (hboundary :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ differenceSubspace →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ differenceSubspace →
        z ∈ (chainDotBilinForm G.edgeSet).orthogonal generatorSubspace →
          AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z) :
    generatorSubspace = differenceSubspace :=
  theorem49_relative_submodule_spanning_of_planarBoundaryHeightOrderedFacePeelWitnessData
    emb data C0 hC0
    (Theorem49RelativeSubmoduleDualityData.ofChainDot
      differenceSubspace generatorSubspace hle hboundary horth)

/-- Chain-dot specialization of the relative finite-collar submodule spanning theorem. -/
theorem theorem49_chainDot_relative_spanning_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (differenceSubspace generatorSubspace : Submodule F2 (G.edgeSet → Color))
    (hle : generatorSubspace ≤ differenceSubspace)
    (hboundary :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ differenceSubspace →
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ differenceSubspace →
        z ∈ (chainDotBilinForm G.edgeSet).orthogonal generatorSubspace →
          AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z) :
    generatorSubspace = differenceSubspace :=
  theorem49_relative_submodule_spanning_of_planarBoundaryCollarLayerFacePeelWitnessData
    emb data C0 hC0
    (Theorem49RelativeSubmoduleDualityData.ofChainDot
      differenceSubspace generatorSubspace hle hboundary horth)

/-- Graph-level height-ordered submodule bridge: an admissible witnessing embedding is enough to
run any same-embedding `Theorem49SubmoduleDualityData` package through the spanning gap. -/
theorem exists_theorem49_submodule_spanning_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V} [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (algebraOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb →
        Theorem49SubmoduleDualityData emb C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        (algebraOf emb data).generatorSubspace = (algebraOf emb data).differenceSubspace := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49_submodule_spanning_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C0 hC0 (algebraOf emb data)⟩

/-- Graph-level finite-collar submodule bridge. -/
theorem exists_theorem49_submodule_spanning_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (algebraOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb →
        Theorem49SubmoduleDualityData emb C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        (algebraOf emb data).generatorSubspace = (algebraOf emb data).differenceSubspace := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49_submodule_spanning_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C0 hC0 (algebraOf emb data)⟩

/-- Graph-level height-ordered chain-dot bridge.  This wrapper constructs the concrete
`Theorem49SubmoduleDualityData` package from same-embedding subspaces and identification lemmas. -/
theorem exists_theorem49_chainDot_spanning_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (generatorSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        generatorSubspaceOf emb data ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ (chainDotBilinForm G.edgeSet).orthogonal (generatorSubspaceOf emb data) →
            AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        generatorSubspaceOf emb data = differenceSubspaceOf emb data := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49_chainDot_spanning_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C0 hC0 (differenceSubspaceOf emb data) (generatorSubspaceOf emb data)
      (hle emb data) (hboundary emb data) (horth emb data)⟩

/-- Graph-level finite-collar chain-dot bridge. -/
theorem exists_theorem49_chainDot_spanning_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (generatorSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        generatorSubspaceOf emb data ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ (chainDotBilinForm G.edgeSet).orthogonal (generatorSubspaceOf emb data) →
            AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        generatorSubspaceOf emb data = differenceSubspaceOf emb data := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49_chainDot_spanning_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C0 hC0 (differenceSubspaceOf emb data) (generatorSubspaceOf emb data)
      (hle emb data) (hboundary emb data) (horth emb data)⟩

/-- Graph-level height-ordered relative submodule bridge. -/
theorem exists_theorem49_relative_submodule_spanning_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V} [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (algebraOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb →
        Theorem49RelativeSubmoduleDualityData emb C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        (algebraOf emb data).generatorSubspace = (algebraOf emb data).differenceSubspace := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49_relative_submodule_spanning_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C0 hC0 (algebraOf emb data)⟩

/-- Graph-level finite-collar relative submodule bridge. -/
theorem exists_theorem49_relative_submodule_spanning_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V} [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (algebraOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb →
        Theorem49RelativeSubmoduleDualityData emb C0) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        (algebraOf emb data).generatorSubspace = (algebraOf emb data).differenceSubspace := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49_relative_submodule_spanning_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C0 hC0 (algebraOf emb data)⟩

/-- Graph-level height-ordered chain-dot bridge for the relative submodule interface. -/
theorem exists_theorem49_chainDot_relative_spanning_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (generatorSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        generatorSubspaceOf emb data ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
          z ∈ (chainDotBilinForm G.edgeSet).orthogonal (generatorSubspaceOf emb data) →
            AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        generatorSubspaceOf emb data = differenceSubspaceOf emb data := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49_chainDot_relative_spanning_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C0 hC0 (differenceSubspaceOf emb data) (generatorSubspaceOf emb data)
      (hle emb data) (hboundary emb data) (horth emb data)⟩

/-- Graph-level finite-collar chain-dot bridge for the relative submodule interface. -/
theorem exists_theorem49_chainDot_relative_spanning_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C0 : G.EdgeColoring Color) (hC0 : IsTaitEdgeColoring G C0)
    (differenceSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (generatorSubspaceOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Submodule F2 (G.edgeSet → Color))
    (hle : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        generatorSubspaceOf emb data ≤ differenceSubspaceOf emb data)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
            ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ differenceSubspaceOf emb data →
          z ∈ (chainDotBilinForm G.edgeSet).orthogonal (generatorSubspaceOf emb data) →
            AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C0 z) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        generatorSubspaceOf emb data = differenceSubspaceOf emb data := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49_chainDot_relative_spanning_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C0 hC0 (differenceSubspaceOf emb data) (generatorSubspaceOf emb data)
      (hle emb data) (hboundary emb data) (horth emb data)⟩

end Mettapedia.GraphTheory.FourColor
