import Mettapedia.GraphTheory.FourColor.Theorem49KempeGeneratorSpan

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- The finite set of graph edges incident to a vertex, viewed in the current `edgeSet` type. -/
def incidentEdgeFinset (G : SimpleGraph V) [Fintype G.edgeSet] (v : V) :
    Finset G.edgeSet :=
  Finset.univ.filter fun e => v ∈ (e : Sym2 V)

/-- The unoriented `𝔽₂²` Kirchhoff sum of a chain at a vertex.  Over `𝔽₂`, orientations are
irrelevant, so this is the natural cycle-space boundary operator for the current color algebra. -/
def vertexKirchhoffSum (G : SimpleGraph V) [Fintype G.edgeSet]
    (x : G.edgeSet → Color) (v : V) : Color :=
  Finset.sum (incidentEdgeFinset G v) fun e => x e

/-- Chains satisfying the Kirchhoff condition at the selected vertices.  The v23 proof applies
this to the interior vertices of the annular triangulation; that vertex set is not yet part of
`PlaneEmbeddingWithBoundary`, so it is explicit here. -/
def kirchhoffSubmodule (G : SimpleGraph V) [Fintype G.edgeSet]
    (vertices : Finset V) : Submodule F2 (G.edgeSet → Color) where
  carrier := {x | ∀ v ∈ vertices, vertexKirchhoffSum G x v = 0}
  zero_mem' := by
    intro v hv
    unfold vertexKirchhoffSum
    simp
  add_mem' := by
    intro x y hx hy v hv
    unfold vertexKirchhoffSum
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    have hxv := hx v hv
    have hyv := hy v hv
    unfold vertexKirchhoffSum at hxv hyv
    rw [hxv, hyv]
    simp
  smul_mem' := by
    intro a x hx v hv
    unfold vertexKirchhoffSum
    simp only [Pi.smul_apply]
    rw [← Finset.smul_sum]
    have hxv := hx v hv
    unfold vertexKirchhoffSum at hxv
    rw [hxv]
    simp

theorem mem_kirchhoffSubmodule {G : SimpleGraph V} [Fintype G.edgeSet]
    {vertices : Finset V} {x : G.edgeSet → Color} :
    x ∈ kirchhoffSubmodule G vertices ↔
      ∀ v ∈ vertices, vertexKirchhoffSum G x v = 0 :=
  Iff.rfl

/-- Chains vanishing on a specified boundary support. -/
def boundaryZeroSubmodule {E : Type*} [DecidableEq E] (boundary : Finset E) :
    Submodule F2 (E → Color) where
  carrier := {x | ∀ e ∈ boundary, x e = 0}
  zero_mem' := by
    intro e he
    rfl
  add_mem' := by
    intro x y hx hy e he
    simp [hx e he, hy e he]
  smul_mem' := by
    intro a x hx e he
    simp [hx e he]

theorem mem_boundaryZeroSubmodule {E : Type*} [DecidableEq E]
    {boundary : Finset E} {x : E → Color} :
    x ∈ boundaryZeroSubmodule boundary ↔ ∀ e ∈ boundary, x e = 0 :=
  Iff.rfl

theorem boundaryZeroSubmodule_le_of_subset {E : Type*} [DecidableEq E]
    {boundary₁ boundary₂ : Finset E} (hsubset : boundary₂ ⊆ boundary₁) :
    boundaryZeroSubmodule boundary₁ ≤ boundaryZeroSubmodule boundary₂ := by
  intro x hx e he
  exact hx e (hsubset he)

/-- Boundary-zero chains for a fixed plane embedding with boundary. -/
def planarBoundaryZeroSubmodule {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) :
    Submodule F2 (G.edgeSet → Color) :=
  boundaryZeroSubmodule
    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)

theorem boundaryZero_of_mem_planarBoundaryZeroSubmodule {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G} {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0 :=
  hz

/-- The concrete v23-shaped target side available from the current interfaces: Kirchhoff at an
explicit vertex set and zero on the selected boundary edges.  Instantiating `vertices` with the
interior vertices is the next upstream data obligation. -/
def theorem49BoundaryZeroKirchhoffSubspace {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V) :
    Submodule F2 (G.edgeSet → Color) :=
  kirchhoffSubmodule G vertices ⊓ planarBoundaryZeroSubmodule emb

theorem theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ≤ planarBoundaryZeroSubmodule emb :=
  inf_le_right

theorem boundaryZero_of_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {vertices : Finset V} {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0 :=
  boundaryZero_of_mem_planarBoundaryZeroSubmodule hz.2

theorem kirchhoff_of_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {vertices : Finset V} {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∀ v ∈ vertices, vertexKirchhoffSum G z v = 0 :=
  hz.1

theorem exists_nonzero_color_ne (c : Color) : ∃ γ : Color, γ ≠ 0 ∧ γ ≠ c := by
  by_cases hc : c = red
  · refine ⟨blue, blue_ne_zero, ?_⟩
    rw [hc]
    intro h
    exact red_ne_blue h.symm
  · exact ⟨red, red_ne_zero, fun h => hc h.symm⟩

/-- A face generator touching a selected boundary edge is not boundary-zero.  This is the
formal warning that the raw all-face simplified generator family cannot be used directly as a
subspace of the v23 `W0(H)` target. -/
theorem polarizedFaceGenerator_not_mem_planarBoundaryZeroSubmodule_of_mem_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (C : G.EdgeColoring Color) {f : emb.Face} {e : G.edgeSet} {γ : Color}
    (heBoundary : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (heFace : e ∈ emb.faceBoundary f) (hγ0 : γ ≠ 0) :
    polarizedFaceGenerator C (C e) (C e + γ) (emb.faceBoundary f) ∉
      planarBoundaryZeroSubmodule emb := by
  intro hmem
  have hzero := boundaryZero_of_mem_planarBoundaryZeroSubmodule hmem e heBoundary
  have hvalue :
      polarizedFaceGenerator C (C e) (C e + γ) (emb.faceBoundary f) e = γ := by
    rw [polarizedFaceGenerator_eq_indicatorChain_of_add_pair]
    exact indicatorChain_apply_of_mem γ
      ((mem_boundaryBicoloredEdges_iff C (C e) (C e + γ)).2 ⟨heFace, Or.inl rfl⟩)
  rw [hvalue] at hzero
  exact hγ0 hzero

theorem polarizedFaceGenerator_mem_kempeClosureGeneratorSubspace
    {G : SimpleGraph V} {F : Type*} {faceBoundary : F → Finset G.edgeSet}
    {C₀ C : G.EdgeColoring Color} {f : F} {a b : Color}
    (hC : C ∈ G.EdgeKempeClosure C₀) (hab : ValidColorPair a b) :
    polarizedFaceGenerator C a b (faceBoundary f) ∈
      kempeClosureGeneratorSubspace faceBoundary C₀ :=
  Submodule.subset_span ⟨C, hC, f, a, b, hab, rfl⟩

/-- The raw simplified Kempe-closure generator span cannot be contained in the selected-boundary
zero subspace as soon as it contains a face generator touching a selected boundary edge.  A later
Theorem 4.9 target must therefore use the purified/difference-space source from v23, or restrict
the generator family before asking for containment in `W0(H)`. -/
theorem not_kempeClosureGeneratorSubspace_le_planarBoundaryZeroSubmodule_of_mem_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {f : emb.Face} {e : G.edgeSet}
    (heBoundary : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (heFace : e ∈ emb.faceBoundary f) :
    ¬ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ planarBoundaryZeroSubmodule emb := by
  intro hle
  rcases exists_nonzero_color_ne (C₀ e) with ⟨γ, hγ0, hγne⟩
  have hvalid : ValidColorPair (C₀ e) (C₀ e + γ) :=
    validColorPair_edgeColor_add_generator C₀ e (hC₀ e) hγ0 hγne
  have hgen :
      polarizedFaceGenerator C₀ (C₀ e) (C₀ e + γ) (emb.faceBoundary f) ∈
        kempeClosureGeneratorSubspace emb.faceBoundary C₀ :=
    polarizedFaceGenerator_mem_kempeClosureGeneratorSubspace
      (SimpleGraph.mem_edgeKempeClosure_self C₀) hvalid
  exact
    polarizedFaceGenerator_not_mem_planarBoundaryZeroSubmodule_of_mem_selectedBoundarySupport
      C₀ heBoundary heFace hγ0 (hle hgen)

theorem not_kempeClosureGeneratorSubspace_le_boundaryZeroKirchhoffSubspace_of_mem_selectedBoundarySupport
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {f : emb.Face} {e : G.edgeSet} {vertices : Finset V}
    (heBoundary : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (heFace : e ∈ emb.faceBoundary f) :
    ¬ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤
      theorem49BoundaryZeroKirchhoffSubspace emb vertices := by
  intro hle
  exact
    not_kempeClosureGeneratorSubspace_le_planarBoundaryZeroSubmodule_of_mem_selectedBoundarySupport
      C₀ hC₀ heBoundary heFace
      (fun x hx =>
        theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices
          (hle hx))

theorem not_exists_vertices_kempeClosureGeneratorSubspace_le_boundaryZeroKirchhoffSubspace_of_mem_selectedBoundarySupport
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {f : emb.Face} {e : G.edgeSet}
    (heBoundary : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (heFace : e ∈ emb.faceBoundary f) :
    ¬ ∃ vertices : Finset V,
      kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤
        theorem49BoundaryZeroKirchhoffSubspace emb vertices := by
  rintro ⟨vertices, hle⟩
  exact
    not_kempeClosureGeneratorSubspace_le_boundaryZeroKirchhoffSubspace_of_mem_selectedBoundarySupport
      C₀ hC₀ heBoundary heFace hle

/-- The Kempe-generator span constructor specialized to a target already known to lie inside the
selected-boundary-zero submodule. -/
noncomputable def Theorem49SubmoduleDualityData.ofKempeGeneratorSubspaceLeBoundaryZero
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    [Fintype G.edgeSet]
    (differenceSubspace : Submodule F2 (G.edgeSet → Color))
    (hleGenerator : kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤ differenceSubspace)
    (hleBoundary : differenceSubspace ≤ planarBoundaryZeroSubmodule emb) :
    Theorem49SubmoduleDualityData emb C₀ :=
  Theorem49SubmoduleDualityData.ofKempeGeneratorSubspace
    differenceSubspace hleGenerator (by
      intro z hz
      exact boundaryZero_of_mem_planarBoundaryZeroSubmodule (hleBoundary hz))

/-- Theorem 4.9 with the target side named as the boundary-zero Kirchhoff subspace.  The containment
hypothesis is intentionally explicit: the obstruction above shows that the current raw all-face
simplified generator span does not satisfy it when boundary-face generators are present. -/
theorem theorem49_kempeGeneratorSubspace_eq_boundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hleGenerator :
      kempeClosureGeneratorSubspace emb.faceBoundary C₀ ≤
        theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    kempeClosureGeneratorSubspace emb.faceBoundary C₀ =
      theorem49BoundaryZeroKirchhoffSubspace emb vertices :=
  theorem49_submodule_spanning_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    emb data C₀ hC₀
    (Theorem49SubmoduleDualityData.ofKempeGeneratorSubspaceLeBoundaryZero
      (theorem49BoundaryZeroKirchhoffSubspace emb vertices)
      hleGenerator
      (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices))

end Mettapedia.GraphTheory.FourColor
