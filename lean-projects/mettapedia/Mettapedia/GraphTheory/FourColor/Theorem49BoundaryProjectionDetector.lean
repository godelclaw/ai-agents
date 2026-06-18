import Mettapedia.GraphTheory.FourColor.Theorem49SynthesisClosureInvariance

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Detector form of the selected-boundary annihilator endpoint: every nonzero selected-
boundary-zero chain pairs nontrivially with some projected Definition 4.8 generator.  This is
the exact hypothesis shape exposed by the current finite lab certificates. -/
def BoundaryZeroProjectedGeneratorDetector {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) : Prop :=
  ∀ ⦃z : G.edgeSet → Color⦄,
    z ∈ planarBoundaryZeroSubmodule emb →
    z ≠ 0 →
      ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p z ≠ 0

/-- The detector property depends only on the underlying edge-Kempe closure class of the chosen
base coloring.  This is the algebraic transport step needed to upgrade a single explicit finite
certificate to a whole closure class. -/
theorem BoundaryZeroProjectedGeneratorDetector.of_edgeKempeClosure_eq
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ C₁ : G.EdgeColoring Color}
    (hclosure : G.EdgeKempeClosure C₀ = G.EdgeKempeClosure C₁)
    (h : BoundaryZeroProjectedGeneratorDetector emb C₀) :
    BoundaryZeroProjectedGeneratorDetector emb C₁ := by
  intro z hzBoundary hzNonzero
  rcases h hzBoundary hzNonzero with ⟨p, hp, hpair⟩
  have hproj :
      projectedKempeClosureGeneratorSubspace emb C₀ =
        projectedKempeClosureGeneratorSubspace emb C₁ :=
    projectedKempeClosureGeneratorSubspace_eq_of_edgeKempeClosure_eq hclosure
  exact ⟨p, by simpa [hproj] using hp, hpair⟩

/-- Mutual edge-Kempe reachability is enough to transport the detector property between base
colorings. -/
theorem BoundaryZeroProjectedGeneratorDetector.of_mutual_edgeKempeReachability
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ C₁ : G.EdgeColoring Color}
    (h : BoundaryZeroProjectedGeneratorDetector emb C₀)
    (h₀₁ : C₁ ∈ G.EdgeKempeClosure C₀) (h₁₀ : C₀ ∈ G.EdgeKempeClosure C₁) :
    BoundaryZeroProjectedGeneratorDetector emb C₁ :=
  BoundaryZeroProjectedGeneratorDetector.of_edgeKempeClosure_eq
    (G := G) (emb := emb) (C₀ := C₀) (C₁ := C₁)
    (G.edgeKempeClosure_eq_of_mem_of_mem h₀₁ h₁₀) h

/-- The already-proved boundary-zero annihilator endpoint implies the detector form used by the
finite lab: a nonzero selected-boundary-zero chain cannot be orthogonal to the projected
Definition 4.8 generator span. -/
theorem BoundaryZeroProjectedGeneratorDetector.of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀) :
    BoundaryZeroProjectedGeneratorDetector emb C₀ := by
  intro z hzBoundary hzNonzero
  by_contra hnone
  have hzOrth :
      z ∈ (chainDotBilinForm G.edgeSet).orthogonal
        (projectedKempeClosureGeneratorSubspace emb C₀) := by
    intro p hp
    by_contra hpair
    exact hnone ⟨p, hp, hpair⟩
  have hzAnnih :
      AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z :=
    annihilatesKempeClosureGeneratorFamily_of_boundaryZero_of_mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace
      (G := G) (emb := emb) (C₀ := C₀) (z := z) hzBoundary hzOrth
  have hzZero : z = 0 := by
    funext e
    exact htrivial z (boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary) hzAnnih e
  exact hzNonzero hzZero

/-- Detector form as an honest orthogonal-triviality statement on the selected-boundary-zero
subspace.  This is the direct linear-algebra form of the finite lab certificate: no nonzero
selected-boundary-zero chain lies in the orthogonal complement of the projected Definition 4.8
generator span. -/
theorem planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_boundaryZeroProjectedGeneratorDetector
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    (hdet : BoundaryZeroProjectedGeneratorDetector emb C₀) :
    planarBoundaryZeroSubmodule emb ⊓
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedKempeClosureGeneratorSubspace emb C₀) =
      ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  by_contra hzNonzero
  rcases hdet hz.1 hzNonzero with ⟨p, hp, hpair⟩
  exact hpair (hz.2 p hp)

/-- Conversely, orthogonal-triviality on the selected-boundary-zero subspace is already the full
detector property. -/
theorem boundaryZeroProjectedGeneratorDetector_of_planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    (hbot : planarBoundaryZeroSubmodule emb ⊓
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedKempeClosureGeneratorSubspace emb C₀) =
      ⊥) :
    BoundaryZeroProjectedGeneratorDetector emb C₀ := by
  intro z hzBoundary hzNonzero
  by_contra hnone
  have hzOrth :
      z ∈ (chainDotBilinForm G.edgeSet).orthogonal
        (projectedKempeClosureGeneratorSubspace emb C₀) := by
    intro p hp
    by_contra hpair
    exact hnone ⟨p, hp, hpair⟩
  have hzBot :
      z ∈ (⊥ : Submodule F2 (G.edgeSet → Color)) := by
    rw [← hbot]
    exact ⟨hzBoundary, hzOrth⟩
  exact hzNonzero (by simpa using hzBot)

/-- Bidirectional form of the detector criterion: the finite certificate is exactly the claim
that the selected-boundary-zero subspace meets the orthogonal complement of the projected
generator span only at zero. -/
theorem boundaryZeroProjectedGeneratorDetector_iff_planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color} :
    BoundaryZeroProjectedGeneratorDetector emb C₀ ↔
      planarBoundaryZeroSubmodule emb ⊓
          (chainDotBilinForm G.edgeSet).orthogonal
            (projectedKempeClosureGeneratorSubspace emb C₀) =
        ⊥ := by
  constructor
  · exact
      planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_boundaryZeroProjectedGeneratorDetector
  · exact
      boundaryZeroProjectedGeneratorDetector_of_planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot

/-- Pointwise orthogonality characterization on the whole selected-boundary-zero subspace under
the detector hypothesis. -/
theorem planarBoundaryZeroSubmodule_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_boundaryZeroProjectedGeneratorDetector
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    (hdet : BoundaryZeroProjectedGeneratorDetector emb C₀)
    {z : G.edgeSet → Color} (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p z = 0) ↔
      z = 0 := by
  constructor
  · intro hzero
    by_contra hzNonzero
    rcases hdet hz hzNonzero with ⟨p, hp, hpair⟩
    exact hpair (hzero p hp)
  · intro hzZero p _hp
    rw [hzZero]
    exact (chainDotBilinForm G.edgeSet p).map_zero

/-- Conversely, a detector on all selected-boundary-zero chains is already enough to recover the
full boundary-zero annihilator endpoint.  This is the algebraic bridge from finite detector
certificates back to the existing theorem-4.9 synthesis route. -/
theorem boundaryZeroAnnihilatorTrivialForEmbedding_of_boundaryZeroProjectedGeneratorDetector
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    (hdet : BoundaryZeroProjectedGeneratorDetector emb C₀) :
    BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀ := by
  intro z hzeroBoundary hAnnih e
  have hzBoundary : z ∈ planarBoundaryZeroSubmodule emb := hzeroBoundary
  have hzZero : z = 0 := by
    by_contra hzNonzero
    rcases hdet hzBoundary hzNonzero with ⟨p, hp, hpair⟩
    have hzOrth :
        z ∈ (chainDotBilinForm G.edgeSet).orthogonal
          (projectedKempeClosureGeneratorSubspace emb C₀) :=
      mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_of_boundaryZero_of_annihilatesKempeClosureGeneratorFamily
        (G := G) (emb := emb) (C₀ := C₀) (z := z) hzBoundary hAnnih
    exact hpair (hzOrth p hp)
  simp [hzZero]

/-- A boundary-zero projected-generator detector is enough to prove the corrected projected
Definition 4.8 spanning statement. -/
theorem projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroProjectedGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (hdet : BoundaryZeroProjectedGeneratorDetector emb C₀) :
    projectedKempeClosureGeneratorSubspace emb C₀ = planarBoundaryZeroSubmodule emb := by
  exact submodule_eq_of_le_of_inf_orthogonal_eq_bot
    (B := chainDotBilinForm G.edgeSet)
    (hB := chainDotBilinForm_nondegenerate (E := G.edgeSet))
    (hB₀ := chainDotBilinForm_isRefl (E := G.edgeSet))
    (projectedKempeClosureGeneratorSubspace_le_planarBoundaryZeroSubmodule emb C₀)
    (planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_boundaryZeroProjectedGeneratorDetector
      hdet)

/-- Family-span form of the detector conclusion: the selected-boundary-erased Definition 4.8
generator family spans all selected-boundary-zero chains. -/
theorem span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_boundaryZeroProjectedGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (hdet : BoundaryZeroProjectedGeneratorDetector emb C₀) :
    Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
      planarBoundaryZeroSubmodule emb := by
  rw [← projectedKempeClosureGeneratorSubspace_eq_span_projectedKempeClosureGeneratorFamily]
  exact
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroProjectedGeneratorDetector
      emb C₀ hdet

/-- Operational finite-combination form of the detector route: every selected-boundary-zero chain
is a finite sum of selected-boundary-erased Definition 4.8 generators. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_planarBoundaryZeroSubmodule_of_boundaryZeroProjectedGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (hdet : BoundaryZeroProjectedGeneratorDetector emb C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z := by
  apply
    exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_span_projectedKempeClosureGeneratorFamily
  rw [span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_boundaryZeroProjectedGeneratorDetector
    emb C₀ hdet]
  exact hz

/-- Detector-route finite-combination form for the concrete theorem-4.9 boundary-zero Kirchhoff
target. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryZeroProjectedGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (hdet : BoundaryZeroProjectedGeneratorDetector emb C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z :=
  exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_planarBoundaryZeroSubmodule_of_boundaryZeroProjectedGeneratorDetector
    emb C₀ hdet
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices hz)

/-- Detector-route pointwise separation on the concrete theorem-4.9 target `W₀(H)`. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_boundaryZeroProjectedGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (hdet : BoundaryZeroProjectedGeneratorDetector emb C₀)
    (vertices : Finset V)
    {z : theorem49BoundaryZeroKirchhoffSubspace emb vertices} :
    (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
      z = 0 := by
  constructor
  · intro hzero
    apply Subtype.ext
    exact
      (planarBoundaryZeroSubmodule_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_boundaryZeroProjectedGeneratorDetector
        hdet
        (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices z.property)).1
        hzero
  · intro hz p hp
    rw [hz]
    exact (chainDotBilinForm G.edgeSet p).map_zero

/-- Detector-route kernel-zero statement for the concrete pairing map from `W₀(H)` into the dual
of the projected Definition 4.8 generator span. -/
theorem ker_theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap_eq_bot_of_boundaryZeroProjectedGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (hdet : BoundaryZeroProjectedGeneratorDetector emb C₀)
    (vertices : Finset V) :
    LinearMap.ker
        (theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
          (G := G) emb C₀ vertices) =
      ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  exact
    (theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_boundaryZeroProjectedGeneratorDetector
      (G := G) emb C₀ hdet vertices (z := z)).1
      (by
        intro p hp
        let p' : projectedKempeClosureGeneratorSubspace emb C₀ := ⟨p, hp⟩
        have hmap :
            theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
                (G := G) emb C₀ vertices z = 0 := hz
        have hcoord := congrArg
          (fun f : projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2 => f p') hmap
        simpa [theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap, p'] using
          hcoord)

/-- Finite-dimensional detector consequence: the concrete theorem-4.9 target `W₀(H)` has
dimension at most the projected Definition 4.8 generator span. -/
theorem finrank_theorem49BoundaryZeroKirchhoffSubspace_le_finrank_projectedKempeClosureGeneratorSubspace_of_boundaryZeroProjectedGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (hdet : BoundaryZeroProjectedGeneratorDetector emb C₀)
    (vertices : Finset V) :
    Module.finrank F2 (theorem49BoundaryZeroKirchhoffSubspace emb vertices) ≤
      Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀) := by
  let L :=
    theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
      (G := G) emb C₀ vertices
  have hker : LinearMap.ker L = ⊥ :=
    ker_theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap_eq_bot_of_boundaryZeroProjectedGeneratorDetector
      (G := G) emb C₀ hdet vertices
  have hinj : Function.Injective L := (LinearMap.ker_eq_bot).1 hker
  have hleDual :
      Module.finrank F2 (theorem49BoundaryZeroKirchhoffSubspace emb vertices) ≤
        Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2) :=
    LinearMap.finrank_le_finrank_of_injective (f := L) hinj
  simpa [L, Module.Dual] using
    hleDual.trans_eq
      (Subspace.dual_finrank_eq
        (K := F2) (V := projectedKempeClosureGeneratorSubspace emb C₀))

/-- The same detector hypothesis already reaches the full current theorem-4.9 synthesis package.
Once a finite certificate proves nontrivial pairing against every nonzero selected-boundary-zero
chain, no additional theorem-4.9 algebra remains. -/
theorem theorem49BoundaryRootSynthesis_of_boundaryZeroProjectedGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (hdet : BoundaryZeroProjectedGeneratorDetector emb C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroAnnihilatorTrivial
    (G := G) (emb := emb) C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_boundaryZeroProjectedGeneratorDetector hdet)

end Mettapedia.GraphTheory.FourColor
