import Mettapedia.GraphTheory.FourColor.Theorem49ColoringGeneratorFamilyRoute

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Family-span form of the arbitrary-coloring detector: a nonzero selected-boundary-zero chain
cannot lie in the orthogonal complement of the projected explicit-family span. -/
theorem planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedColoringGeneratorSubspace_eq_bot_of_boundaryZeroProjectedColoringGeneratorDetector
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {colorings : Set (G.EdgeColoring Color)}
    (hdet : BoundaryZeroProjectedColoringGeneratorDetector emb colorings) :
    planarBoundaryZeroSubmodule emb ⊓
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedColoringGeneratorSubspace emb colorings) =
      ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  by_contra hzNonzero
  rcases hdet hz.1 hzNonzero with ⟨p, hp, hpair⟩
  exact hpair (hz.2 p hp)

/-- Conversely, orthogonal-triviality on the selected-boundary-zero subspace is already the full
explicit-family detector property. -/
theorem boundaryZeroProjectedColoringGeneratorDetector_of_planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedColoringGeneratorSubspace_eq_bot
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {colorings : Set (G.EdgeColoring Color)}
    (hbot : planarBoundaryZeroSubmodule emb ⊓
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedColoringGeneratorSubspace emb colorings) =
      ⊥) :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings := by
  intro z hzBoundary hzNonzero
  by_contra hnone
  have hzOrth :
      z ∈ (chainDotBilinForm G.edgeSet).orthogonal
        (projectedColoringGeneratorSubspace emb colorings) := by
    intro p hp
    by_contra hpair
    exact hnone ⟨p, hp, hpair⟩
  have hzBot :
      z ∈ (⊥ : Submodule F2 (G.edgeSet → Color)) := by
    rw [← hbot]
    exact ⟨hzBoundary, hzOrth⟩
  exact hzNonzero (by simpa using hzBot)

/-- Bidirectional form of the explicit-family detector criterion: the finite certificate is
exactly the claim that the selected-boundary-zero subspace meets the orthogonal complement of the
projected explicit-family span only at zero. -/
theorem boundaryZeroProjectedColoringGeneratorDetector_iff_planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedColoringGeneratorSubspace_eq_bot
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {colorings : Set (G.EdgeColoring Color)} :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings ↔
      planarBoundaryZeroSubmodule emb ⊓
          (chainDotBilinForm G.edgeSet).orthogonal
            (projectedColoringGeneratorSubspace emb colorings) =
        ⊥ := by
  constructor
  · exact
      planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedColoringGeneratorSubspace_eq_bot_of_boundaryZeroProjectedColoringGeneratorDetector
  · exact
      boundaryZeroProjectedColoringGeneratorDetector_of_planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedColoringGeneratorSubspace_eq_bot

/-- The explicit-family detector depends only on the projected explicit-family span. -/
theorem BoundaryZeroProjectedColoringGeneratorDetector.of_projectedColoringGeneratorSubspace_eq
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings₀ colorings₁ : Set (G.EdgeColoring Color)}
    (hsub :
      projectedColoringGeneratorSubspace emb colorings₀ =
        projectedColoringGeneratorSubspace emb colorings₁)
    (h : BoundaryZeroProjectedColoringGeneratorDetector emb colorings₀) :
    BoundaryZeroProjectedColoringGeneratorDetector emb colorings₁ := by
  apply
    boundaryZeroProjectedColoringGeneratorDetector_of_planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedColoringGeneratorSubspace_eq_bot
  simpa [hsub] using
    planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedColoringGeneratorSubspace_eq_bot_of_boundaryZeroProjectedColoringGeneratorDetector
      h

/-- The projected explicit-family span is all of the selected-boundary-zero subspace as soon as
the family detects every nonzero selected-boundary-zero chain. -/
theorem projectedColoringGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroProjectedColoringGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (colorings : Set (G.EdgeColoring Color))
    (hdet : BoundaryZeroProjectedColoringGeneratorDetector emb colorings) :
    projectedColoringGeneratorSubspace emb colorings = planarBoundaryZeroSubmodule emb := by
  exact submodule_eq_of_le_of_inf_orthogonal_eq_bot
    (B := chainDotBilinForm G.edgeSet)
    (hB := chainDotBilinForm_nondegenerate (E := G.edgeSet))
    (hB₀ := chainDotBilinForm_isRefl (E := G.edgeSet))
    (projectedColoringGeneratorSubspace_le_planarBoundaryZeroSubmodule emb colorings)
    (planarBoundaryZeroSubmodule_inf_chainDot_orthogonal_projectedColoringGeneratorSubspace_eq_bot_of_boundaryZeroProjectedColoringGeneratorDetector
      hdet)

/-- The projected explicit coloring-family span is exactly the selected-boundary-zero subspace. -/
theorem span_projectedColoringGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_boundaryZeroProjectedColoringGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (colorings : Set (G.EdgeColoring Color))
    (hdet : BoundaryZeroProjectedColoringGeneratorDetector emb colorings) :
    Submodule.span F2 (projectedColoringGeneratorFamily emb colorings) =
      planarBoundaryZeroSubmodule emb := by
  rw [← projectedColoringGeneratorSubspace_eq_span_projectedColoringGeneratorFamily]
  exact
    projectedColoringGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroProjectedColoringGeneratorDetector
      emb colorings hdet

/-- Pointwise orthogonality characterization on the whole selected-boundary-zero subspace under
the explicit-family detector hypothesis. -/
theorem planarBoundaryZeroSubmodule_chainDot_projectedColoringGeneratorSubspace_eq_zero_iff_of_boundaryZeroProjectedColoringGeneratorDetector
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {colorings : Set (G.EdgeColoring Color)}
    (hdet : BoundaryZeroProjectedColoringGeneratorDetector emb colorings)
    {z : G.edgeSet → Color} (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    (∀ p ∈ projectedColoringGeneratorSubspace emb colorings,
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

/-- Membership in the explicit projected family span is witnessed by a finite sum of projected
family generators. -/
theorem exists_projectedColoringGeneratorFamily_finset_sum_of_mem_span_projectedColoringGeneratorFamily
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)} {z : G.edgeSet → Color}
    (hz : z ∈ Submodule.span F2 (projectedColoringGeneratorFamily emb colorings)) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedColoringGeneratorFamily emb colorings ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z :=
  (Submodule.mem_span_iff_exists_finset_subset
    (R := F2) (s := projectedColoringGeneratorFamily emb colorings) (x := z)).1 hz

/-- Operational detector consequence for explicit families: every selected-boundary-zero chain is
an honest finite sum of projected generators from the detecting family. -/
theorem exists_projectedColoringGeneratorFamily_finset_sum_of_mem_planarBoundaryZeroSubmodule_of_boundaryZeroProjectedColoringGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (colorings : Set (G.EdgeColoring Color))
    (hdet : BoundaryZeroProjectedColoringGeneratorDetector emb colorings)
    {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedColoringGeneratorFamily emb colorings ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z := by
  apply exists_projectedColoringGeneratorFamily_finset_sum_of_mem_span_projectedColoringGeneratorFamily
  rw [span_projectedColoringGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_boundaryZeroProjectedColoringGeneratorDetector
    emb colorings hdet]
  exact hz

/-- The same finite-sum reconstruction applies in particular to the theorem-4.9 Kirchhoff target
subspace `W₀(H)`. -/
theorem exists_projectedColoringGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryZeroProjectedColoringGeneratorDetector
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (colorings : Set (G.EdgeColoring Color))
    (hdet : BoundaryZeroProjectedColoringGeneratorDetector emb colorings)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedColoringGeneratorFamily emb colorings ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z :=
  exists_projectedColoringGeneratorFamily_finset_sum_of_mem_planarBoundaryZeroSubmodule_of_boundaryZeroProjectedColoringGeneratorDetector
    emb colorings hdet
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices hz)

end Mettapedia.GraphTheory.FourColor
