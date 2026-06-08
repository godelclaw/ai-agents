import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mettapedia.GraphTheory.FourColor.Theorem49TargetSubspace

namespace Mettapedia.GraphTheory.FourColor

open LinearMap

variable {V : Type*} [DecidableEq V]

/-- The coordinate projection that erases a chosen boundary support. -/
def boundaryZeroProjection {E : Type*} [DecidableEq E] (boundary : Finset E) :
    (E → Color) →ₗ[F2] (E → Color) where
  toFun x e := if e ∈ boundary then 0 else x e
  map_add' := by
    intro x y
    funext e
    by_cases he : e ∈ boundary <;> simp [he]
  map_smul' := by
    intro a x
    funext e
    by_cases he : e ∈ boundary <;> simp [he]

@[simp] theorem boundaryZeroProjection_apply_of_mem {E : Type*} [DecidableEq E]
    {boundary : Finset E} {x : E → Color} {e : E} (he : e ∈ boundary) :
    boundaryZeroProjection boundary x e = 0 := by
  simp [boundaryZeroProjection, he]

@[simp] theorem boundaryZeroProjection_apply_of_not_mem {E : Type*} [DecidableEq E]
    {boundary : Finset E} {x : E → Color} {e : E} (he : e ∉ boundary) :
    boundaryZeroProjection boundary x e = x e := by
  simp [boundaryZeroProjection, he]

theorem boundaryZeroProjection_mem_boundaryZeroSubmodule {E : Type*} [DecidableEq E]
    {boundary : Finset E} (x : E → Color) :
    boundaryZeroProjection boundary x ∈ boundaryZeroSubmodule boundary := by
  intro e he
  exact boundaryZeroProjection_apply_of_mem he

theorem boundaryZeroProjection_eq_self_of_mem_boundaryZeroSubmodule
    {E : Type*} [DecidableEq E] {boundary : Finset E} {x : E → Color}
    (hx : x ∈ boundaryZeroSubmodule boundary) :
    boundaryZeroProjection boundary x = x := by
  funext e
  by_cases he : e ∈ boundary
  · simp [boundaryZeroProjection, he, hx e he]
  · simp [boundaryZeroProjection, he]

theorem boundaryZeroProjection_eq_self_iff_mem_boundaryZeroSubmodule
    {E : Type*} [DecidableEq E] {boundary : Finset E} {x : E → Color} :
    boundaryZeroProjection boundary x = x ↔ x ∈ boundaryZeroSubmodule boundary := by
  constructor
  · intro hx
    rw [← hx]
    exact boundaryZeroProjection_mem_boundaryZeroSubmodule x
  · exact boundaryZeroProjection_eq_self_of_mem_boundaryZeroSubmodule

theorem boundaryZeroProjection_idempotent
    {E : Type*} [DecidableEq E] {boundary : Finset E} (x : E → Color) :
    boundaryZeroProjection boundary (boundaryZeroProjection boundary x) =
      boundaryZeroProjection boundary x :=
  boundaryZeroProjection_eq_self_of_mem_boundaryZeroSubmodule
    (boundaryZeroProjection_mem_boundaryZeroSubmodule x)

theorem range_boundaryZeroProjection_eq_boundaryZeroSubmodule
    {E : Type*} [DecidableEq E] {boundary : Finset E} :
    LinearMap.range (boundaryZeroProjection boundary) = boundaryZeroSubmodule boundary := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact boundaryZeroProjection_mem_boundaryZeroSubmodule y
  · intro hx
    exact ⟨x, boundaryZeroProjection_eq_self_of_mem_boundaryZeroSubmodule hx⟩

theorem range_selectedBoundaryProjection_eq_planarBoundaryZeroSubmodule
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    LinearMap.range
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) =
      planarBoundaryZeroSubmodule emb :=
  range_boundaryZeroProjection_eq_boundaryZeroSubmodule

/-- Chains supported only on a specified boundary support.  This is the coordinate kernel of
`boundaryZeroProjection`: all non-boundary coordinates vanish. -/
def boundarySupportedSubmodule {E : Type*} [DecidableEq E] (boundary : Finset E) :
    Submodule F2 (E → Color) where
  carrier := {x | ∀ e, e ∉ boundary → x e = 0}
  zero_mem' := by
    intro e he
    rfl
  add_mem' := by
    intro x y hx hy e he
    simp [hx e he, hy e he]
  smul_mem' := by
    intro a x hx e he
    simp [hx e he]

theorem mem_boundarySupportedSubmodule {E : Type*} [DecidableEq E]
    {boundary : Finset E} {x : E → Color} :
    x ∈ boundarySupportedSubmodule boundary ↔ ∀ e, e ∉ boundary → x e = 0 :=
  Iff.rfl

theorem boundaryZeroProjection_eq_zero_iff_mem_boundarySupportedSubmodule
    {E : Type*} [DecidableEq E] {boundary : Finset E} {x : E → Color} :
    boundaryZeroProjection boundary x = 0 ↔ x ∈ boundarySupportedSubmodule boundary := by
  constructor
  · intro hx e he
    have hcoord := congrFun hx e
    simpa [boundaryZeroProjection, he] using hcoord
  · intro hx
    funext e
    by_cases he : e ∈ boundary
    · simp [boundaryZeroProjection, he]
    · simp [boundaryZeroProjection, he, hx e he]

theorem boundarySupportedSubmodule_eq_ker_boundaryZeroProjection
    {E : Type*} [DecidableEq E] {boundary : Finset E} :
    boundarySupportedSubmodule boundary = LinearMap.ker (boundaryZeroProjection boundary) := by
  ext x
  exact (boundaryZeroProjection_eq_zero_iff_mem_boundarySupportedSubmodule
    (boundary := boundary) (x := x)).symm

theorem add_mem_boundarySupportedSubmodule_of_boundaryZeroProjection_eq
    {E : Type*} [DecidableEq E] {boundary : Finset E} {x y : E → Color}
    (h : boundaryZeroProjection boundary y = boundaryZeroProjection boundary x) :
    y + x ∈ boundarySupportedSubmodule boundary := by
  intro e he
  have hcoord := congrFun h e
  simp [boundaryZeroProjection, he] at hcoord
  change y e + x e = 0
  rw [hcoord]
  exact color_add_self (x e)

theorem boundaryZeroProjection_eq_iff_add_mem_boundarySupportedSubmodule
    {E : Type*} [DecidableEq E] {boundary : Finset E} {x y : E → Color} :
    boundaryZeroProjection boundary y = boundaryZeroProjection boundary x ↔
      y + x ∈ boundarySupportedSubmodule boundary := by
  constructor
  · exact add_mem_boundarySupportedSubmodule_of_boundaryZeroProjection_eq
  · intro h
    funext e
    by_cases he : e ∈ boundary
    · simp [boundaryZeroProjection, he]
    · have hcoord := h e he
      change y e + x e = 0 at hcoord
      have hyeq : y e = x e := (add_eq_zero_iff_eq (y e) (x e)).mp hcoord
      simp [boundaryZeroProjection, he, hyeq]

theorem boundaryZeroProjection_eq_iff_add_mem_ker_boundaryZeroProjection
    {E : Type*} [DecidableEq E] {boundary : Finset E} {x y : E → Color} :
    boundaryZeroProjection boundary y = boundaryZeroProjection boundary x ↔
      y + x ∈ LinearMap.ker (boundaryZeroProjection boundary) := by
  rw [← boundarySupportedSubmodule_eq_ker_boundaryZeroProjection]
  exact boundaryZeroProjection_eq_iff_add_mem_boundarySupportedSubmodule

theorem boundaryZeroProjection_eq_iff_add_mem_submodule_inf_boundarySupportedSubmodule
    {E : Type*} [DecidableEq E] {boundary : Finset E}
    {S : Submodule F2 (E → Color)} {x y : E → Color}
    (hx : x ∈ S) (hy : y ∈ S) :
    boundaryZeroProjection boundary y = boundaryZeroProjection boundary x ↔
      y + x ∈ S ⊓ boundarySupportedSubmodule boundary := by
  constructor
  · intro h
    exact ⟨S.add_mem hy hx,
      (boundaryZeroProjection_eq_iff_add_mem_boundarySupportedSubmodule
        (boundary := boundary) (x := x) (y := y)).1 h⟩
  · intro h
    exact
      (boundaryZeroProjection_eq_iff_add_mem_boundarySupportedSubmodule
        (boundary := boundary) (x := x) (y := y)).2 h.2

theorem mem_ker_boundaryZeroProjection_domRestrict_submodule_iff
    {E : Type*} [DecidableEq E] {boundary : Finset E}
    {S : Submodule F2 (E → Color)} {x : S} :
    x ∈ LinearMap.ker ((boundaryZeroProjection boundary).domRestrict S) ↔
      (x : E → Color) ∈ boundarySupportedSubmodule boundary := by
  change boundaryZeroProjection boundary (x : E → Color) = 0 ↔
    (x : E → Color) ∈ boundarySupportedSubmodule boundary
  exact boundaryZeroProjection_eq_zero_iff_mem_boundarySupportedSubmodule

theorem ker_boundaryZeroProjection_domRestrict_submodule_eq_comap_boundarySupportedSubmodule
    {E : Type*} [DecidableEq E] {boundary : Finset E}
    {S : Submodule F2 (E → Color)} :
    LinearMap.ker ((boundaryZeroProjection boundary).domRestrict S) =
      Submodule.comap S.subtype (boundarySupportedSubmodule boundary) := by
  ext x
  exact mem_ker_boundaryZeroProjection_domRestrict_submodule_iff

/-- First-isomorphism form of selected-boundary erasure restricted to an arbitrary submodule. -/
noncomputable def boundaryZeroProjectionSubmoduleQuotientEquivImage
    {E : Type*} [DecidableEq E] (boundary : Finset E)
    (S : Submodule F2 (E → Color)) :
    (S ⧸ LinearMap.ker ((boundaryZeroProjection boundary).domRestrict S)) ≃ₗ[F2]
      Submodule.map (boundaryZeroProjection boundary) S :=
  ((boundaryZeroProjection boundary).domRestrict S).quotKerEquivRange.trans
    (LinearEquiv.ofEq _ _
      (LinearMap.range_domRestrict S (boundaryZeroProjection boundary)))

theorem boundaryZeroProjectionSubmoduleQuotientEquivImage_apply_mk
    {E : Type*} [DecidableEq E] {boundary : Finset E}
    {S : Submodule F2 (E → Color)} (x : S) :
    ((boundaryZeroProjectionSubmoduleQuotientEquivImage boundary S
        (Submodule.Quotient.mk x) :
        Submodule.map (boundaryZeroProjection boundary) S) :
        E → Color) =
      boundaryZeroProjection boundary (x : E → Color) := by
  rw [boundaryZeroProjectionSubmoduleQuotientEquivImage]
  simp [LinearMap.quotKerEquivRange_apply_mk]

theorem boundaryZeroProjectionSubmoduleQuotient_mk_eq_mk_iff
    {E : Type*} [DecidableEq E] {boundary : Finset E}
    {S : Submodule F2 (E → Color)} {x y : S} :
    (Submodule.Quotient.mk x :
        S ⧸ LinearMap.ker ((boundaryZeroProjection boundary).domRestrict S)) =
        Submodule.Quotient.mk y ↔
      boundaryZeroProjection boundary (x : E → Color) =
        boundaryZeroProjection boundary (y : E → Color) := by
  rw [Submodule.Quotient.eq]
  change boundaryZeroProjection boundary ((x : E → Color) - (y : E → Color)) = 0 ↔ _
  rw [map_sub]
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h

theorem boundaryZeroProjectionSubmoduleQuotient_mk_eq_mk_iff_add_mem
    {E : Type*} [DecidableEq E] {boundary : Finset E}
    {S : Submodule F2 (E → Color)} {x y : S} :
    (Submodule.Quotient.mk x :
        S ⧸ LinearMap.ker ((boundaryZeroProjection boundary).domRestrict S)) =
        Submodule.Quotient.mk y ↔
      (y : E → Color) + (x : E → Color) ∈
        S ⊓ boundarySupportedSubmodule boundary := by
  rw [boundaryZeroProjectionSubmoduleQuotient_mk_eq_mk_iff]
  rw [eq_comm]
  exact boundaryZeroProjection_eq_iff_add_mem_submodule_inf_boundarySupportedSubmodule
    (boundary := boundary) (S := S) (x := (x : E → Color)) (y := (y : E → Color))
    x.property y.property

theorem boundaryZeroProjectionSubmoduleQuotient_mk_eq_zero_iff
    {E : Type*} [DecidableEq E] {boundary : Finset E}
    {S : Submodule F2 (E → Color)} {x : S} :
    (Submodule.Quotient.mk x :
        S ⧸ LinearMap.ker ((boundaryZeroProjection boundary).domRestrict S)) = 0 ↔
      (x : E → Color) ∈ boundarySupportedSubmodule boundary := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_ker_boundaryZeroProjection_domRestrict_submodule_iff

theorem boundaryZeroProjection_eq_iff_add_mem_kirchhoffSubmodule_inf_boundarySupportedSubmodule
    {G : SimpleGraph V} [Fintype G.edgeSet] {boundary : Finset G.edgeSet}
    {vertices : Finset V} {x y : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G vertices) (hy : y ∈ kirchhoffSubmodule G vertices) :
    boundaryZeroProjection boundary y = boundaryZeroProjection boundary x ↔
      y + x ∈ kirchhoffSubmodule G vertices ⊓ boundarySupportedSubmodule boundary := by
  rw [boundarySupportedSubmodule_eq_ker_boundaryZeroProjection]
  constructor
  · intro h
    exact ⟨(kirchhoffSubmodule G vertices).add_mem hy hx,
      (boundaryZeroProjection_eq_iff_add_mem_ker_boundaryZeroProjection
        (boundary := boundary) (x := x) (y := y)).1 h⟩
  · intro h
    exact
      (boundaryZeroProjection_eq_iff_add_mem_ker_boundaryZeroProjection
        (boundary := boundary) (x := x) (y := y)).2 h.2

theorem selectedBoundaryProjection_eq_iff_add_mem_kirchhoffSubmodule_inf_boundarySupportedSubmodule
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {vertices : Finset V} {x y : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G vertices) (hy : y ∈ kirchhoffSubmodule G vertices) :
    boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y =
        boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x ↔
      y + x ∈
        kirchhoffSubmodule G vertices ⊓
          boundarySupportedSubmodule
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :=
  boundaryZeroProjection_eq_iff_add_mem_kirchhoffSubmodule_inf_boundarySupportedSubmodule
    (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (vertices := vertices) hx hy

theorem selectedBoundaryProjection_eq_iff_add_mem_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_inf_boundarySupportedSubmodule
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color} {vertices : Finset V} {x y : G.edgeSet → Color}
    (hx :
      x ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices)
    (hy :
      y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) :
    boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y =
        boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x ↔
      y + x ∈
        (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) ⊓
          boundarySupportedSubmodule
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :=
  boundaryZeroProjection_eq_iff_add_mem_submodule_inf_boundarySupportedSubmodule
    (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (S := kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices)
    hx hy

theorem selectedBoundaryProjectionKempeKirchhoffQuotient_mk_eq_mk_iff
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color} {vertices : Finset V}
    {x y : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
        kirchhoffSubmodule G vertices)} :
    (Submodule.Quotient.mk x :
        ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G vertices) ⧸
          LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                  kirchhoffSubmodule G vertices))) =
        Submodule.Quotient.mk y ↔
      boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
          (x : G.edgeSet → Color) =
        boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
          (y : G.edgeSet → Color) :=
  boundaryZeroProjectionSubmoduleQuotient_mk_eq_mk_iff
    (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (S := kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices)

theorem selectedBoundaryProjectionKempeKirchhoffQuotient_mk_eq_mk_iff_add_mem
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color} {vertices : Finset V}
    {x y : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
        kirchhoffSubmodule G vertices)} :
    (Submodule.Quotient.mk x :
        ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G vertices) ⧸
          LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                  kirchhoffSubmodule G vertices))) =
        Submodule.Quotient.mk y ↔
      (y : G.edgeSet → Color) + (x : G.edgeSet → Color) ∈
        (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) ⊓
          boundarySupportedSubmodule
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :=
  boundaryZeroProjectionSubmoduleQuotient_mk_eq_mk_iff_add_mem
    (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (S := kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices)

theorem selectedBoundaryProjectionKempeKirchhoffQuotient_mk_eq_zero_iff
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color} {vertices : Finset V}
    {x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
        kirchhoffSubmodule G vertices)} :
    (Submodule.Quotient.mk x :
        ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G vertices) ⧸
          LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                  kirchhoffSubmodule G vertices))) = 0 ↔
      (x : G.edgeSet → Color) ∈
        boundarySupportedSubmodule
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :=
  boundaryZeroProjectionSubmoduleQuotient_mk_eq_zero_iff
    (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (S := kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices)

theorem mem_ker_boundaryZeroProjection_domRestrict_kirchhoffSubmodule_iff
    {G : SimpleGraph V} [Fintype G.edgeSet] {boundary : Finset G.edgeSet}
    {vertices : Finset V} {x : kirchhoffSubmodule G vertices} :
    x ∈ LinearMap.ker
        ((boundaryZeroProjection boundary).domRestrict (kirchhoffSubmodule G vertices)) ↔
      (x : G.edgeSet → Color) ∈ boundarySupportedSubmodule boundary := by
  change boundaryZeroProjection boundary (x : G.edgeSet → Color) = 0 ↔
    (x : G.edgeSet → Color) ∈ boundarySupportedSubmodule boundary
  exact boundaryZeroProjection_eq_zero_iff_mem_boundarySupportedSubmodule

theorem ker_boundaryZeroProjection_domRestrict_kirchhoffSubmodule_eq_comap_boundarySupportedSubmodule
    {G : SimpleGraph V} [Fintype G.edgeSet] {boundary : Finset G.edgeSet}
    {vertices : Finset V} :
    LinearMap.ker
        ((boundaryZeroProjection boundary).domRestrict (kirchhoffSubmodule G vertices)) =
      Submodule.comap (kirchhoffSubmodule G vertices).subtype
        (boundarySupportedSubmodule boundary) := by
  ext x
  exact mem_ker_boundaryZeroProjection_domRestrict_kirchhoffSubmodule_iff

/-- First-isomorphism form of the raw Kirchhoff boundary-erasure quotient.  The source quotient is
the raw Kirchhoff submodule modulo the restricted selected-boundary kernel, and the target is the
selected-boundary-erased raw Kirchhoff image. -/
noncomputable def boundaryZeroProjectionKirchhoffQuotientEquivImage
    {G : SimpleGraph V} [Fintype G.edgeSet] (boundary : Finset G.edgeSet)
    (vertices : Finset V) :
    (kirchhoffSubmodule G vertices ⧸
      LinearMap.ker
        ((boundaryZeroProjection boundary).domRestrict (kirchhoffSubmodule G vertices))) ≃ₗ[F2]
      Submodule.map (boundaryZeroProjection boundary) (kirchhoffSubmodule G vertices) :=
  ((boundaryZeroProjection boundary).domRestrict
      (kirchhoffSubmodule G vertices)).quotKerEquivRange.trans
    (LinearEquiv.ofEq _ _
      (LinearMap.range_domRestrict
        (kirchhoffSubmodule G vertices) (boundaryZeroProjection boundary)))

theorem boundaryZeroProjectionKirchhoffQuotientEquivImage_apply_mk
    {G : SimpleGraph V} [Fintype G.edgeSet] {boundary : Finset G.edgeSet}
    {vertices : Finset V} (x : kirchhoffSubmodule G vertices) :
    ((boundaryZeroProjectionKirchhoffQuotientEquivImage
        (G := G) boundary vertices
        (Submodule.Quotient.mk x) :
        Submodule.map (boundaryZeroProjection boundary) (kirchhoffSubmodule G vertices)) :
        G.edgeSet → Color) =
      boundaryZeroProjection boundary (x : G.edgeSet → Color) := by
  rw [boundaryZeroProjectionKirchhoffQuotientEquivImage]
  simp [LinearMap.quotKerEquivRange_apply_mk]

theorem chain_add_self_add (x y : E → Color) :
    x + (x + y) = y := by
  funext e
  change x e + (x e + y e) = y e
  rw [← add_assoc]
  simp

/-- A boundary-zero left input cannot see the erased boundary coordinates of the right input. -/
theorem chainDotBilinForm_boundaryZeroProjection_right_eq_of_left_boundaryZero
    {E : Type*} [Fintype E] [DecidableEq E]
    {boundary : Finset E} {x y : E → Color}
    (hx : x ∈ boundaryZeroSubmodule boundary) :
    chainDotBilinForm E x (boundaryZeroProjection boundary y) =
      chainDotBilinForm E x y := by
  classical
  rw [chainDotBilinForm_apply, chainDotBilinForm_apply]
  refine Finset.sum_congr rfl ?_
  intro e he
  by_cases hb : e ∈ boundary
  · simp [hb, hx e hb]
  · simp [hb]

/-- Erasing a boundary support does not change the Kirchhoff sum at a vertex not incident to that
support.  This is the local algebraic form of the "interior vertex" side condition in `W₀(H)`. -/
theorem vertexKirchhoffSum_boundaryZeroProjection_eq_of_boundary_avoids_vertex
    {G : SimpleGraph V} [Fintype G.edgeSet] {boundary : Finset G.edgeSet}
    {x : G.edgeSet → Color} {v : V}
    (hboundary : ∀ e ∈ boundary, v ∉ (e : Sym2 V)) :
    vertexKirchhoffSum G (boundaryZeroProjection boundary x) v =
      vertexKirchhoffSum G x v := by
  classical
  unfold vertexKirchhoffSum incidentEdgeFinset
  refine Finset.sum_congr rfl ?_
  intro e he
  have hv : v ∈ (e : Sym2 V) := (Finset.mem_filter.mp he).2
  have hnot : e ∉ boundary := fun heb => hboundary e heb hv
  simp [boundaryZeroProjection, hnot]

/-- If every erased boundary edge avoids a finite vertex set, boundary projection preserves the
Kirchhoff condition at exactly those vertices. -/
theorem boundaryZeroProjection_mem_kirchhoffSubmodule_iff_of_boundary_avoids_vertices
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {boundary : Finset G.edgeSet} {vertices : Finset V} {x : G.edgeSet → Color}
    (hboundary : ∀ v ∈ vertices, ∀ e ∈ boundary, v ∉ (e : Sym2 V)) :
    boundaryZeroProjection boundary x ∈ kirchhoffSubmodule G vertices ↔
      x ∈ kirchhoffSubmodule G vertices := by
  constructor
  · intro hx v hv
    have hsum :=
      vertexKirchhoffSum_boundaryZeroProjection_eq_of_boundary_avoids_vertex
        (G := G) (boundary := boundary) (x := x) (v := v) (hboundary v hv)
    rw [← hsum]
    exact hx v hv
  · intro hx v hv
    have hsum :=
      vertexKirchhoffSum_boundaryZeroProjection_eq_of_boundary_avoids_vertex
        (G := G) (boundary := boundary) (x := x) (v := v) (hboundary v hv)
    rw [hsum]
    exact hx v hv

/-- On a vertex set disjoint from the selected boundary support, membership of a projected chain
in the concrete boundary-zero Kirchhoff target is exactly the raw Kirchhoff condition before
projection. -/
theorem boundaryZeroProjection_mem_theorem49BoundaryZeroKirchhoffSubspace_iff_of_selectedBoundary_avoids_vertices
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {vertices : Finset V} {x : G.edgeSet → Color}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x ∈
        theorem49BoundaryZeroKirchhoffSubspace emb vertices ↔
      x ∈ kirchhoffSubmodule G vertices := by
  constructor
  · intro hx
    exact
      (boundaryZeroProjection_mem_kirchhoffSubmodule_iff_of_boundary_avoids_vertices
        (G := G)
        (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
        (vertices := vertices) (x := x) hboundary).1 hx.1
  · intro hx
    refine ⟨?_, ?_⟩
    · exact
        (boundaryZeroProjection_mem_kirchhoffSubmodule_iff_of_boundary_avoids_vertices
          (G := G)
          (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
          (vertices := vertices) (x := x) hboundary).2 hx
    · exact boundaryZeroProjection_mem_boundaryZeroSubmodule x

/-- With the selected-boundary support disjoint from the chosen target vertices, the concrete
boundary-zero Kirchhoff target is exactly the image of the raw Kirchhoff submodule under boundary
erasure. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kirchhoffSubmodule_of_selectedBoundary_avoids_vertices
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices =
      Submodule.map
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
        (kirchhoffSubmodule G vertices) := by
  ext z
  constructor
  · intro hz
    refine ⟨z, hz.1, ?_⟩
    exact boundaryZeroProjection_eq_self_of_mem_boundaryZeroSubmodule hz.2
  · rintro ⟨x, hx, rfl⟩
    exact
      (boundaryZeroProjection_mem_theorem49BoundaryZeroKirchhoffSubspace_iff_of_selectedBoundary_avoids_vertices
        (G := G) (emb := emb) (vertices := vertices) (x := x) hboundary).2 hx

/-- First-isomorphism form landing directly in the concrete v23 target `W₀(H)`.  The side condition
is the same interior-vertex/boundary-support disjointness hypothesis used to identify the target
with the selected-boundary-erased Kirchhoff image. -/
noncomputable def selectedBoundaryProjectionKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V} [Fintype G.edgeSet] (emb : PlaneEmbeddingWithBoundary G)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    (kirchhoffSubmodule G vertices ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            (kirchhoffSubmodule G vertices))) ≃ₗ[F2]
      theorem49BoundaryZeroKirchhoffSubspace emb vertices :=
  (boundaryZeroProjectionKirchhoffQuotientEquivImage
      (G := G)
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) vertices).trans
    (LinearEquiv.ofEq _ _
      (theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kirchhoffSubmodule_of_selectedBoundary_avoids_vertices
        (G := G) (emb := emb) (vertices := vertices) hboundary).symm)

theorem selectedBoundaryProjectionKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_apply_mk
    {G : SimpleGraph V} [Fintype G.edgeSet] {emb : PlaneEmbeddingWithBoundary G}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    (x : kirchhoffSubmodule G vertices) :
    ((selectedBoundaryProjectionKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace
        (G := G) emb vertices hboundary
        (Submodule.Quotient.mk x) :
        theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
        G.edgeSet → Color) =
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
        (x : G.edgeSet → Color) := by
  rw [selectedBoundaryProjectionKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace]
  simp [boundaryZeroProjectionKirchhoffQuotientEquivImage_apply_mk]

/-- The Definition 4.8 generator span after erasing the selected boundary coordinates.  This is the
boundary-compatible source suggested by the annihilator proof: the raw face generators are used as
tests, but the spanning subspace inside `W₀` must use their boundary-erased images. -/
noncomputable def projectedKempeClosureGeneratorSubspace
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) :
    Submodule F2 (G.edgeSet → Color) :=
  Submodule.map
    (boundaryZeroProjection
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (kempeClosureGeneratorSubspace emb.faceBoundary C₀)

/-- The boundary-compatible Definition 4.8 generator family: each raw face generator is projected
off the selected boundary support before being used as a spanning generator. -/
def projectedKempeClosureGeneratorFamily
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) :
    Set (G.edgeSet → Color) :=
  (boundaryZeroProjection
    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ''
      kempeClosureGeneratorFamily emb.faceBoundary C₀

theorem mem_projectedKempeClosureGeneratorFamily_iff
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {x : G.edgeSet → Color} :
    x ∈ projectedKempeClosureGeneratorFamily emb C₀ ↔
      ∃ C ∈ G.EdgeKempeClosure C₀, ∃ f : emb.Face, ∃ a b : Color,
        ValidColorPair a b ∧
          x =
            boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (polarizedFaceGenerator C a b (emb.faceBoundary f)) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases (mem_kempeClosureGeneratorFamily_iff emb.faceBoundary C₀ y).1 hy with
      ⟨C, hC, f, a, b, hab, rfl⟩
    exact ⟨C, hC, f, a, b, hab, rfl⟩
  · rintro ⟨C, hC, f, a, b, hab, rfl⟩
    refine ⟨polarizedFaceGenerator C a b (emb.faceBoundary f), ?_, rfl⟩
    exact (mem_kempeClosureGeneratorFamily_iff emb.faceBoundary C₀
      (polarizedFaceGenerator C a b (emb.faceBoundary f))).2
      ⟨C, hC, f, a, b, hab, rfl⟩

/-- The corrected projected source is exactly the span of the boundary-erased Definition 4.8
generators. -/
theorem projectedKempeClosureGeneratorSubspace_eq_span_projectedKempeClosureGeneratorFamily
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) :
    projectedKempeClosureGeneratorSubspace emb C₀ =
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
  rw [projectedKempeClosureGeneratorSubspace, projectedKempeClosureGeneratorFamily,
    kempeClosureGeneratorSubspace, Submodule.map_span]

/-- Membership in the explicit projected family span is witnessed by a finite sum of projected
Definition 4.8 generators.  The coefficients are represented as a finitely supported function by
requiring its support to lie in the finite set of terms. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_span_projectedKempeClosureGeneratorFamily
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {z : G.edgeSet → Color}
    (hz : z ∈ Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀)) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z :=
  (Submodule.mem_span_iff_exists_finset_subset
    (R := F2) (s := projectedKempeClosureGeneratorFamily emb C₀) (x := z)).1 hz

theorem projectedKempeClosureGeneratorSubspace_le_planarBoundaryZeroSubmodule
    {G : SimpleGraph V} (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) :
    projectedKempeClosureGeneratorSubspace emb C₀ ≤ planarBoundaryZeroSubmodule emb := by
  intro x hx
  rcases (Submodule.mem_map.mp hx) with ⟨y, _hy, rfl⟩
  exact boundaryZeroProjection_mem_boundaryZeroSubmodule y

/-- Membership in the projected source is represented by an honest raw Definition 4.8 generator
combination whose selected-boundary projection is the given chain. -/
theorem exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_projectedKempeClosureGeneratorSubspace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {z : G.edgeSet → Color}
    (hz : z ∈ projectedKempeClosureGeneratorSubspace emb C₀) :
    ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀,
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z :=
  Submodule.mem_map.mp hz

/-- Membership in the projected source is witnessed by a finite raw Definition 4.8 generator
combination before applying the selected-boundary projection. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_projectedKempeClosureGeneratorSubspace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {z : G.edgeSet → Color}
    (hz : z ∈ projectedKempeClosureGeneratorSubspace emb C₀) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (∑ y ∈ terms, coeff y • y) = z := by
  rcases
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_projectedKempeClosureGeneratorSubspace
      hz with
    ⟨y, hy, hproj⟩
  have hyspan :
      y ∈ Submodule.span F2 (kempeClosureGeneratorFamily emb.faceBoundary C₀) := by
    simpa [kempeClosureGeneratorSubspace] using hy
  rcases
    (Submodule.mem_span_iff_exists_finset_subset
      (R := F2) (s := kempeClosureGeneratorFamily emb.faceBoundary C₀) (x := y)).1
      hyspan with
    ⟨coeff, terms, hterms, hsupport, hsum⟩
  refine ⟨coeff, terms, hterms, hsupport, ?_⟩
  rw [hsum]
  exact hproj

theorem projectedKempeClosureGenerator_mem_projectedKempeClosureGeneratorSubspace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} {C₀ C : G.EdgeColoring Color}
    {f : emb.Face} {a b : Color}
    (hC : C ∈ G.EdgeKempeClosure C₀) (hab : ValidColorPair a b) :
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
        (polarizedFaceGenerator C a b (emb.faceBoundary f)) ∈
      projectedKempeClosureGeneratorSubspace emb C₀ := by
  refine Submodule.mem_map.mpr ?_
  exact ⟨polarizedFaceGenerator C a b (emb.faceBoundary f),
    polarizedFaceGenerator_mem_kempeClosureGeneratorSubspace hC hab, rfl⟩

/-- Orthogonality to the boundary-erased generator span is enough for the raw generator-family
annihilation predicate, provided the testing chain is already boundary-zero. -/
theorem annihilatesKempeClosureGeneratorFamily_of_boundaryZero_of_mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {z : G.edgeSet → Color}
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzOrth : z ∈ (chainDotBilinForm G.edgeSet).orthogonal
      (projectedKempeClosureGeneratorSubspace emb C₀)) :
    AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z := by
  intro C hC f a b hab
  let boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces
  let gen : G.edgeSet → Color := polarizedFaceGenerator C a b (emb.faceBoundary f)
  have hprojMem :
      boundaryZeroProjection boundary gen ∈ projectedKempeClosureGeneratorSubspace emb C₀ := by
    exact projectedKempeClosureGenerator_mem_projectedKempeClosureGeneratorSubspace hC hab
  have horthLeft :
      chainDotBilinForm G.edgeSet (boundaryZeroProjection boundary gen) z = 0 :=
    hzOrth (boundaryZeroProjection boundary gen) hprojMem
  have horthRight :
      chainDotBilinForm G.edgeSet z (boundaryZeroProjection boundary gen) = 0 := by
    calc
      chainDotBilinForm G.edgeSet z (boundaryZeroProjection boundary gen) =
          chainDotBilinForm G.edgeSet (boundaryZeroProjection boundary gen) z := by
            exact (chainDotBilinForm_isSymm G.edgeSet).eq z (boundaryZeroProjection boundary gen)
      _ = 0 := horthLeft
  have hraw :
      chainDotBilinForm G.edgeSet z gen = 0 := by
    rw [← chainDotBilinForm_boundaryZeroProjection_right_eq_of_left_boundaryZero
      (boundary := boundary) (x := z) (y := gen) hzBoundary]
    exact horthRight
  simpa [boundary, gen, chainDotBilinForm_polarizedFaceGenerator_eq_chainDot C z a b
      (emb.faceBoundary f)] using hraw

/-- Conversely, for a boundary-zero chain, annihilating the raw Definition 4.8 generator family
puts the chain in the orthogonal complement of the boundary-erased generator span. -/
theorem mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_of_boundaryZero_of_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {z : G.edgeSet → Color}
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzAnnih : AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z) :
    z ∈ (chainDotBilinForm G.edgeSet).orthogonal
      (projectedKempeClosureGeneratorSubspace emb C₀) := by
  intro x hx
  let boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces
  rcases (Submodule.mem_map.mp hx) with ⟨y, hy, rfl⟩
  have hyOrth :
      chainDotBilinForm G.edgeSet y z = 0 :=
    mem_chainDot_orthogonal_kempeClosureGeneratorSubspace_of_annihilatesKempeClosureGeneratorFamily
      (faceBoundary := emb.faceBoundary) (C₀ := C₀) (z := z) hzAnnih y hy
  calc
    chainDotBilinForm G.edgeSet (boundaryZeroProjection boundary y) z =
        chainDotBilinForm G.edgeSet z (boundaryZeroProjection boundary y) := by
          exact (chainDotBilinForm_isSymm G.edgeSet).eq (boundaryZeroProjection boundary y) z
    _ = chainDotBilinForm G.edgeSet z y := by
      exact chainDotBilinForm_boundaryZeroProjection_right_eq_of_left_boundaryZero
        (boundary := boundary) (x := z) (y := y) hzBoundary
    _ = chainDotBilinForm G.edgeSet y z := by
      exact (chainDotBilinForm_isSymm G.edgeSet).eq z y
    _ = 0 := hyOrth

/-- On boundary-zero chains, orthogonality to the boundary-erased generator span is equivalent to
the route-facing raw generator-family annihilation predicate. -/
theorem mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_iff_annihilatesKempeClosureGeneratorFamily
    {G : SimpleGraph V} [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G} {C₀ : G.EdgeColoring Color}
    {z : G.edgeSet → Color}
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb) :
    z ∈ (chainDotBilinForm G.edgeSet).orthogonal
        (projectedKempeClosureGeneratorSubspace emb C₀) ↔
      AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z := by
  constructor
  · exact
      annihilatesKempeClosureGeneratorFamily_of_boundaryZero_of_mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace
        hzBoundary
  · exact
      mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_of_boundaryZero_of_annihilatesKempeClosureGeneratorFamily
        hzBoundary

/-- The projected generator span instantiates the relative submodule-duality bridge with the
target difference space taken to be all selected-boundary-zero chains. -/
noncomputable def Theorem49RelativeSubmoduleDualityData.ofProjectedKempeClosureGeneratorSubspace
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) :
    Theorem49RelativeSubmoduleDualityData emb C₀ :=
  Theorem49RelativeSubmoduleDualityData.ofChainDot
    (planarBoundaryZeroSubmodule emb)
    (projectedKempeClosureGeneratorSubspace emb C₀)
    (projectedKempeClosureGeneratorSubspace_le_planarBoundaryZeroSubmodule emb C₀)
    (by
      intro z hz
      exact boundaryZero_of_mem_planarBoundaryZeroSubmodule hz)
    (by
      intro z hzDiff hzOrth
      exact
        annihilatesKempeClosureGeneratorFamily_of_boundaryZero_of_mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace
          hzDiff hzOrth)

/-- Annihilator triviality gives a true spanning statement for the boundary-erased generator
source.  Unlike the raw generator span, this source is actually a subspace of the selected-boundary
zero chains. -/
theorem projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀) :
    projectedKempeClosureGeneratorSubspace emb C₀ = planarBoundaryZeroSubmodule emb :=
  (Theorem49RelativeSubmoduleDualityData.ofProjectedKempeClosureGeneratorSubspace
    emb C₀).generatorSubspace_eq_differenceSubspace htrivial

/-- Equivalent family-level form of the projected-source spanning theorem under annihilator
triviality. -/
theorem span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀) :
    Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
      planarBoundaryZeroSubmodule emb := by
  rw [← projectedKempeClosureGeneratorSubspace_eq_span_projectedKempeClosureGeneratorFamily]
  exact projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
    emb C₀ htrivial

/-- The v23-shaped boundary-zero Kirchhoff target is contained in the boundary-erased generator
span once the boundary-zero annihilator is trivial.  This is the corrected inclusion direction:
the raw all-face generator span need not lie in the target, but its selected-boundary projection
spans every boundary-zero Kirchhoff chain. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ≤
      projectedKempeClosureGeneratorSubspace emb C₀ := by
  intro z hz
  rw [projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
    emb C₀ htrivial]
  exact theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices hz

/-- Boundary-zero annihilator triviality separates the concrete `W₀(H)` target from the
orthogonal complement of the corrected projected Definition 4.8 generator span.  This is the
submodule-duality core of the projected-source theorem and does not require the quotient-side
interior-vertex disjointness hypotheses used by the raw-source presentation. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ⊓
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedKempeClosureGeneratorSubspace emb C₀) =
      ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  have hzBoundary : z ∈ planarBoundaryZeroSubmodule emb :=
    theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
      emb vertices hz.1
  have hAnnih :
      AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀ z :=
    annihilatesKempeClosureGeneratorFamily_of_boundaryZero_of_mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace
      (G := G) (emb := emb) (C₀ := C₀) (z := z) hzBoundary hz.2
  exact funext
    (htrivial z (boundaryZero_of_mem_planarBoundaryZeroSubmodule hzBoundary) hAnnih)

/-- Detector form of the projected-source separation theorem: every nonzero concrete `W₀(H)`
chain pairs nontrivially with some vector in the projected Definition 4.8 generator span. -/
theorem exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀)
    (vertices : Finset V)
    {z : theorem49BoundaryZeroKirchhoffSubspace emb vertices}
    (hz : z ≠ 0) :
    ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  classical
  by_contra hnone
  have hzOrth :
      (z : G.edgeSet → Color) ∈
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedKempeClosureGeneratorSubspace emb C₀) := by
    intro p hp
    by_contra hpair
    exact hnone ⟨p, hp, hpair⟩
  have hsep :=
    theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_boundaryZeroAnnihilatorTrivial
      (G := G) emb C₀ htrivial vertices
  have hzBot :
      (z : G.edgeSet → Color) ∈ (⊥ : Submodule F2 (G.edgeSet → Color)) := by
    rw [← hsep]
    exact ⟨z.property, hzOrth⟩
  have hzVal : (z : G.edgeSet → Color) = 0 := by
    simpa using hzBot
  exact hz (Subtype.ext hzVal)

/-- Pointwise orthogonality characterization for the corrected projected-source pairing on
`W₀(H)`. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀)
    (vertices : Finset V)
    {z : theorem49BoundaryZeroKirchhoffSubspace emb vertices} :
    (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
      z = 0 := by
  constructor
  · intro hzero
    by_contra hz
    rcases
      exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryZeroAnnihilatorTrivial
        (G := G) emb C₀ htrivial vertices hz with
      ⟨p, hp, hpair⟩
    exact hpair (hzero p hp)
  · intro hz p _hp
    rw [hz]
    exact (chainDotBilinForm G.edgeSet p).map_zero

/-- Under annihilator triviality, every selected-boundary-zero chain has a raw Definition 4.8
generator-span preimage whose boundary projection is the chain. -/
theorem exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀,
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  apply
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_projectedKempeClosureGeneratorSubspace
  rw [projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
    emb C₀ htrivial]
  exact hz

/-- Under annihilator triviality, every chain in the v23-shaped boundary-zero Kirchhoff target is
the boundary projection of a raw Definition 4.8 generator-span element. -/
theorem exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀,
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z :=
  exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
    emb C₀ htrivial
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices hz)

/-- The certificate-complete Theorem 4.9 annihilator route therefore spans the selected-boundary
zero subspace after boundary projection of the raw Definition 4.8 generators. -/
theorem projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    projectedKempeClosureGeneratorSubspace emb C₀ = planarBoundaryZeroSubmodule emb :=
  projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀)

/-- Family-level form of the corrected Theorem 4.9 source: the span of the selected-boundary-erased
Definition 4.8 generator family is the whole selected-boundary-zero subspace. -/
theorem span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
      planarBoundaryZeroSubmodule emb := by
  rw [← projectedKempeClosureGeneratorSubspace_eq_span_projectedKempeClosureGeneratorFamily]
  exact
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀

/-- Route-facing Theorem 4.9 characterization: under the current interior-dual data, the concrete
boundary-zero Kirchhoff target is exactly the Kirchhoff equations cut down by the projected
Definition 4.8 generator span. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices =
      kirchhoffSubmodule G vertices ⊓ projectedKempeClosureGeneratorSubspace emb C₀ := by
  rw [theorem49BoundaryZeroKirchhoffSubspace,
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀]

/-- Explicit-family form of the same characterization: the target `W0` is the intersection of the
Kirchhoff equations with the span of the boundary-erased Definition 4.8 generator family. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices =
      kirchhoffSubmodule G vertices ⊓
        Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
  rw [theorem49BoundaryZeroKirchhoffSubspace,
    span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀]

/-- The same route-facing inclusion specialized to the interior-dual boundary-rooted peel data:
the concrete boundary-zero Kirchhoff target lies in the projected Definition 4.8 generator span. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ≤
      projectedKempeClosureGeneratorSubspace emb C₀ :=
  theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀)
    vertices

/-- Explicit family-span version of the corrected target inclusion: the concrete boundary-zero
Kirchhoff target is contained in the span of the boundary-erased Definition 4.8 generators. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_le_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ≤
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
  rw [span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    emb data C₀ hC₀]
  exact theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices

/-- Height-ordered witness-cover data is already enough for the corrected projected-source
spanning statement: the selected-boundary-erased Definition 4.8 generator span is the whole
selected-boundary-zero subspace. -/
theorem projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    projectedKempeClosureGeneratorSubspace emb C₀ = planarBoundaryZeroSubmodule emb :=
  projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀)

/-- Finite collar-layer witness-cover data is enough for the corrected projected-source spanning
statement. -/
theorem projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    projectedKempeClosureGeneratorSubspace emb C₀ = planarBoundaryZeroSubmodule emb :=
  projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀)

/-- Family-level height-ordered form of the corrected projected-source spanning theorem. -/
theorem span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
      planarBoundaryZeroSubmodule emb := by
  rw [← projectedKempeClosureGeneratorSubspace_eq_span_projectedKempeClosureGeneratorFamily]
  exact
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀

/-- Family-level finite-collar form of the corrected projected-source spanning theorem. -/
theorem span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
      planarBoundaryZeroSubmodule emb := by
  rw [← projectedKempeClosureGeneratorSubspace_eq_span_projectedKempeClosureGeneratorFamily]
  exact
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀

/-- Family-level local explicit-remainder form of the corrected projected-source spanning
theorem.  This is the weakest currently constructive collar surface exposed directly to the
Definition 4.8 generator span. -/
theorem span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
      planarBoundaryZeroSubmodule emb := by
  rw [← projectedKempeClosureGeneratorSubspace_eq_span_projectedKempeClosureGeneratorFamily]
  exact
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
      emb C₀
      (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
        emb data C₀ hC₀)

/-- Height-ordered witness-cover data identifies the concrete boundary-zero Kirchhoff target with
the Kirchhoff equations cut down by the projected Definition 4.8 generator span. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices =
      kirchhoffSubmodule G vertices ⊓ projectedKempeClosureGeneratorSubspace emb C₀ := by
  rw [theorem49BoundaryZeroKirchhoffSubspace,
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀]

/-- Finite-collar witness-cover data identifies the concrete boundary-zero Kirchhoff target with
the Kirchhoff equations cut down by the projected Definition 4.8 generator span. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices =
      kirchhoffSubmodule G vertices ⊓ projectedKempeClosureGeneratorSubspace emb C₀ := by
  rw [theorem49BoundaryZeroKirchhoffSubspace,
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀]

/-- Height-ordered explicit-family characterization of the concrete boundary-zero Kirchhoff target. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices =
      kirchhoffSubmodule G vertices ⊓
        Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
  rw [theorem49BoundaryZeroKirchhoffSubspace,
    span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀]

/-- Finite-collar explicit-family characterization of the concrete boundary-zero Kirchhoff target. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices =
      kirchhoffSubmodule G vertices ⊓
        Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
  rw [theorem49BoundaryZeroKirchhoffSubspace,
    span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀]

/-- Height-ordered route-facing inclusion: the concrete boundary-zero Kirchhoff target lies in the
projected Definition 4.8 generator span. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ≤
      projectedKempeClosureGeneratorSubspace emb C₀ :=
  theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀)
    vertices

/-- Finite-collar route-facing inclusion: the concrete boundary-zero Kirchhoff target lies in the
projected Definition 4.8 generator span. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ≤
      projectedKempeClosureGeneratorSubspace emb C₀ :=
  theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀)
    vertices

/-- Height-ordered explicit-family inclusion into the corrected projected generator span. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_le_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ≤
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
  rw [span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
    emb data C₀ hC₀]
  exact theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices

/-- Finite-collar explicit-family inclusion into the corrected projected generator span. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_le_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ≤
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
  rw [span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
    emb data C₀ hC₀]
  exact theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices

/-- Height-ordered projected-source separation: the concrete boundary-zero Kirchhoff target has
trivial intersection with the chain-dot orthogonal complement of the projected Definition 4.8
generator span. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ⊓
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedKempeClosureGeneratorSubspace emb C₀) =
      ⊥ :=
  theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀)
    vertices

/-- Finite-collar projected-source separation. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ⊓
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedKempeClosureGeneratorSubspace emb C₀) =
      ⊥ :=
  theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀)
    vertices

/-- Height-ordered pointwise detector form for the corrected projected-source pairing. -/
theorem exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    {z : theorem49BoundaryZeroKirchhoffSubspace emb vertices}
    (hz : z ≠ 0) :
    ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 :=
  exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀)
    vertices hz

/-- Finite-collar pointwise detector form for the corrected projected-source pairing. -/
theorem exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    {z : theorem49BoundaryZeroKirchhoffSubspace emb vertices}
    (hz : z ≠ 0) :
    ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 :=
  exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀)
    vertices hz

/-- Height-ordered pointwise orthogonality characterization against the projected Definition 4.8
generator span. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    {z : theorem49BoundaryZeroKirchhoffSubspace emb vertices} :
    (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
      z = 0 :=
  theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀)
    vertices

/-- Finite-collar pointwise orthogonality characterization against the projected Definition 4.8
generator span. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    {z : theorem49BoundaryZeroKirchhoffSubspace emb vertices} :
    (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
      z = 0 :=
  theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀)
    vertices

/-- Every selected-boundary-zero chain has a finite linear-combination witness using the explicit
boundary-erased Definition 4.8 generator family once the interior-dual route supplies annihilator
triviality. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z := by
  apply
    exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_span_projectedKempeClosureGeneratorFamily
  rw [span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    emb data C₀ hC₀]
  exact hz

/-- Operational finite-combination form for the concrete v23-shaped target: every boundary-zero
Kirchhoff chain is a finite sum of selected-boundary-erased Definition 4.8 generators. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z :=
  exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    emb data C₀ hC₀
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices hz)

/-- With the interior-dual boundary-rooted peel data in hand, every boundary-zero Kirchhoff target
chain has a raw Definition 4.8 generator-span preimage whose selected-boundary projection is that
target chain. -/
theorem exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀,
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z :=
  exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀)
    vertices hz

/-- Every selected-boundary-zero chain is the selected-boundary projection of a finite sum of
unprojected Definition 4.8 generators once the interior-dual route supplies annihilator
triviality. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (∑ y ∈ terms, coeff y • y) = z := by
  apply
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_projectedKempeClosureGeneratorSubspace
  rw [projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    emb data C₀ hC₀]
  exact hz

/-- Finite raw-generator form of the corrected Theorem 4.9 source statement: every target chain
is the selected-boundary projection of a finite sum of unprojected Definition 4.8 generators. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (∑ y ∈ terms, coeff y • y) = z := by
  exact
  exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    emb data C₀ hC₀
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices hz)

/-- Height-ordered operational form: every selected-boundary-zero chain is a finite sum of the
explicit selected-boundary-erased Definition 4.8 generator family. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z := by
  apply
    exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_span_projectedKempeClosureGeneratorFamily
  rw [span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
    emb data C₀ hC₀]
  exact hz

/-- Finite-collar operational form: every selected-boundary-zero chain is a finite sum of the
explicit selected-boundary-erased Definition 4.8 generator family. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z := by
  apply
    exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_span_projectedKempeClosureGeneratorFamily
  rw [span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
    emb data C₀ hC₀]
  exact hz

/-- Local explicit-remainder operational form: every selected-boundary-zero chain is a finite sum
of the explicit selected-boundary-erased Definition 4.8 generator family. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z := by
  apply
    exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_span_projectedKempeClosureGeneratorFamily
  rw [span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    emb data C₀ hC₀]
  exact hz

/-- Height-ordered finite-combination form for the concrete boundary-zero Kirchhoff target. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z :=
  exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
    emb data C₀ hC₀
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices hz)

/-- Finite-collar finite-combination form for the concrete boundary-zero Kirchhoff target. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z :=
  exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
    emb data C₀ hC₀
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices hz)

/-- Local explicit-remainder finite-combination form for the concrete boundary-zero Kirchhoff
target. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
        coeff.support ⊆ terms ∧
          ∑ y ∈ terms, coeff y • y = z :=
  exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    emb data C₀ hC₀
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices hz)

/-- Height-ordered raw-subspace preimage form: every boundary-zero Kirchhoff target chain is the
selected-boundary projection of a raw Definition 4.8 generator-span chain. -/
theorem exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀,
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z :=
  exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀)
    vertices hz

/-- Finite-collar raw-subspace preimage form: every boundary-zero Kirchhoff target chain is the
selected-boundary projection of a raw Definition 4.8 generator-span chain. -/
theorem exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀,
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z :=
  exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀)
    vertices hz

/-- Local explicit-remainder raw-subspace preimage form: every boundary-zero Kirchhoff target chain
is the selected-boundary projection of a raw Definition 4.8 generator-span chain. -/
theorem exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀,
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z :=
  exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_boundaryZeroAnnihilatorTrivial
    emb C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀)
    vertices hz

/-- Height-ordered raw finite-generator form: every selected-boundary-zero chain is the projection
of a finite sum of unprojected Definition 4.8 generators. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (∑ y ∈ terms, coeff y • y) = z := by
  apply
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_projectedKempeClosureGeneratorSubspace
  rw [projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
    emb data C₀ hC₀]
  exact hz

/-- Finite-collar raw finite-generator form: every selected-boundary-zero chain is the projection
of a finite sum of unprojected Definition 4.8 generators. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (∑ y ∈ terms, coeff y • y) = z := by
  apply
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_projectedKempeClosureGeneratorSubspace
  rw [projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
    emb data C₀ hC₀]
  exact hz

/-- Local explicit-remainder raw finite-generator form: every selected-boundary-zero chain is the
projection of a finite sum of unprojected Definition 4.8 generators. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    {z : G.edgeSet → Color}
    (hz : z ∈ planarBoundaryZeroSubmodule emb) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (∑ y ∈ terms, coeff y • y) = z := by
  apply
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_projectedKempeClosureGeneratorSubspace
  rw [projectedKempeClosureGeneratorSubspace_eq_span_projectedKempeClosureGeneratorFamily,
    span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀]
  exact hz

/-- Height-ordered finite raw-generator form of the corrected Theorem 4.9 source statement. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (∑ y ∈ terms, coeff y • y) = z :=
  exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
    emb data C₀ hC₀
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices hz)

/-- Finite-collar finite raw-generator form of the corrected Theorem 4.9 source statement. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (∑ y ∈ terms, coeff y • y) = z :=
  exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
    emb data C₀ hC₀
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices hz)

/-- Local explicit-remainder finite raw-generator form of the corrected Theorem 4.9 source
statement. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V) {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (∑ y ∈ terms, coeff y • y) = z :=
  exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_planarBoundaryZeroSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    emb data C₀ hC₀
    (theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule emb vertices hz)

/-- Local explicit-remainder finite raw-generator form with Kirchhoff retention: if the chosen
target vertices avoid the selected boundary support, the raw Definition 4.8 combination witnessing
a boundary-zero Kirchhoff target chain may be chosen so that the raw sum already satisfies the
Kirchhoff equations at those vertices. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_and_mem_kirchhoffSubmodule_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈ kirchhoffSubmodule G vertices ∧
            boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (∑ y ∈ terms, coeff y • y) = z := by
  rcases
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ vertices hz with
    ⟨coeff, terms, hterms, hsupport, hproj⟩
  refine ⟨coeff, terms, hterms, hsupport, ?_, hproj⟩
  have hprojKirch :
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
          (∑ y ∈ terms, coeff y • y) ∈ kirchhoffSubmodule G vertices := by
    rw [hproj]
    exact hz.1
  exact
    (boundaryZeroProjection_mem_kirchhoffSubmodule_iff_of_boundary_avoids_vertices
      (G := G)
      (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
      (vertices := vertices)
      (x := ∑ y ∈ terms, coeff y • y) hboundary).1 hprojKirch

/-- Local explicit-remainder quotient-style raw Kirchhoff form: every raw Kirchhoff chain has the
same selected-boundary-erased image as a finite raw Definition 4.8 generator combination which
itself remains Kirchhoff at the chosen interior vertices. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_eq_boundaryZeroProjection_of_mem_kirchhoffSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈ kirchhoffSubmodule G vertices ∧
            boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (∑ y ∈ terms, coeff y • y) =
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  have hz :
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x ∈
        theorem49BoundaryZeroKirchhoffSubspace emb vertices :=
    (boundaryZeroProjection_mem_theorem49BoundaryZeroKirchhoffSubspace_iff_of_selectedBoundary_avoids_vertices
      (G := G) (emb := emb) (vertices := vertices) (x := x) hboundary).2 hx
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_and_mem_kirchhoffSubmodule_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ vertices hboundary hz

/-- Local explicit-remainder boundary-kernel form of the raw Kirchhoff representative theorem:
the finite raw Definition 4.8 generator combination differs from the input raw Kirchhoff chain
only by a chain supported on the selected boundary coordinates. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_difference_of_mem_kirchhoffSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈ kirchhoffSubmodule G vertices ∧
            (∑ y ∈ terms, coeff y • y) + x ∈
              boundarySupportedSubmodule
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                  (∑ y ∈ terms, coeff y • y) =
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  rcases
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_eq_boundaryZeroProjection_of_mem_kirchhoffSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ vertices hboundary hx with
    ⟨coeff, terms, hterms, hsupport, hkirch, hproj⟩
  refine ⟨coeff, terms, hterms, hsupport, hkirch, ?_, hproj⟩
  exact
    add_mem_boundarySupportedSubmodule_of_boundaryZeroProjection_eq
      (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
      (x := x) (y := ∑ y ∈ terms, coeff y • y) hproj

/-- Local explicit-remainder decomposition form of the raw Kirchhoff representative theorem:
every raw Kirchhoff chain is a finite raw Definition 4.8 generator combination plus a Kirchhoff
chain supported on the selected boundary coordinates. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_error_decomposition_of_mem_kirchhoffSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (boundaryError : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈ kirchhoffSubmodule G vertices ∧
            boundaryError ∈ kirchhoffSubmodule G vertices ∧
              boundaryError ∈
                boundarySupportedSubmodule
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) =
                    boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  rcases
    exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_difference_of_mem_kirchhoffSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ vertices hboundary hx with
    ⟨coeff, terms, hterms, hsupport, hkirch, hboundaryError, hproj⟩
  let raw : G.edgeSet → Color := ∑ y ∈ terms, coeff y • y
  refine
    ⟨coeff, terms, raw + x, hterms, hsupport, hkirch,
      (kirchhoffSubmodule G vertices).add_mem hkirch hx, hboundaryError, ?_, hproj⟩
  exact chain_add_self_add raw x

/-- Local explicit-remainder kernel form of the raw Kirchhoff representative theorem: the boundary
correction lies in the kernel of the selected-boundary erasure map, inside the same Kirchhoff
submodule. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryKernel_error_decomposition_of_mem_kirchhoffSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (boundaryError : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈ kirchhoffSubmodule G vertices ∧
            boundaryError ∈
                kirchhoffSubmodule G vertices ⊓
                  LinearMap.ker
                    (boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
              (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                    (∑ y ∈ terms, coeff y • y) =
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  rcases
    exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_error_decomposition_of_mem_kirchhoffSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ vertices hboundary hx with
    ⟨coeff, terms, boundaryError, hterms, hsupport, hkirch, herrorKirch, herrorSupported,
      hdecomp, hproj⟩
  refine ⟨coeff, terms, boundaryError, hterms, hsupport, hkirch, ?_, hdecomp, hproj⟩
  constructor
  · exact herrorKirch
  · exact
      (boundaryZeroProjection_eq_zero_iff_mem_boundarySupportedSubmodule
        (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
        (x := boundaryError)).2 herrorSupported

/-- If the chosen target vertices are interior relative to the selected boundary support, the raw
finite Definition 4.8 combination witnessing a boundary-zero Kirchhoff target chain may be chosen
so that the raw sum already satisfies the Kirchhoff equations at those vertices. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_and_mem_kirchhoffSubmodule_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈ kirchhoffSubmodule G vertices ∧
            boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (∑ y ∈ terms, coeff y • y) = z := by
  rcases
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ vertices hz with
    ⟨coeff, terms, hterms, hsupport, hproj⟩
  refine ⟨coeff, terms, hterms, hsupport, ?_, hproj⟩
  have hprojKirch :
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
          (∑ y ∈ terms, coeff y • y) ∈ kirchhoffSubmodule G vertices := by
    rw [hproj]
    exact hz.1
  exact
    (boundaryZeroProjection_mem_kirchhoffSubmodule_iff_of_boundary_avoids_vertices
      (G := G)
      (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
      (vertices := vertices)
      (x := ∑ y ∈ terms, coeff y • y) hboundary).1 hprojKirch

/-- Quotient-style raw Kirchhoff form of the corrected source statement: every raw Kirchhoff chain
has the same selected-boundary-erased image as a finite raw Definition 4.8 generator combination
which itself remains Kirchhoff at the chosen interior vertices. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_eq_boundaryZeroProjection_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈ kirchhoffSubmodule G vertices ∧
            boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (∑ y ∈ terms, coeff y • y) =
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  have hz :
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x ∈
        theorem49BoundaryZeroKirchhoffSubspace emb vertices :=
    (boundaryZeroProjection_mem_theorem49BoundaryZeroKirchhoffSubspace_iff_of_selectedBoundary_avoids_vertices
      (G := G) (emb := emb) (vertices := vertices) (x := x) hboundary).2 hx
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_and_mem_kirchhoffSubmodule_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ vertices hboundary hz

/-- Boundary-kernel form of the raw Kirchhoff representative theorem: the finite raw Definition
4.8 generator combination differs from the input raw Kirchhoff chain only by a chain supported on
the selected boundary coordinates. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_difference_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈ kirchhoffSubmodule G vertices ∧
            (∑ y ∈ terms, coeff y • y) + x ∈
              boundarySupportedSubmodule
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                  (∑ y ∈ terms, coeff y • y) =
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  rcases
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_eq_boundaryZeroProjection_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ vertices hboundary hx with
    ⟨coeff, terms, hterms, hsupport, hkirch, hproj⟩
  refine ⟨coeff, terms, hterms, hsupport, hkirch, ?_, hproj⟩
  exact
    add_mem_boundarySupportedSubmodule_of_boundaryZeroProjection_eq
      (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
      (x := x) (y := ∑ y ∈ terms, coeff y • y) hproj

/-- Decomposition form of the raw Kirchhoff representative theorem: every raw Kirchhoff chain is
a finite raw Definition 4.8 generator combination plus a Kirchhoff chain supported on the selected
boundary coordinates. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_error_decomposition_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (boundaryError : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈ kirchhoffSubmodule G vertices ∧
            boundaryError ∈ kirchhoffSubmodule G vertices ∧
              boundaryError ∈
                boundarySupportedSubmodule
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) =
                    boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  rcases
    exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_difference_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ vertices hboundary hx with
    ⟨coeff, terms, hterms, hsupport, hkirch, hboundaryError, hproj⟩
  let raw : G.edgeSet → Color := ∑ y ∈ terms, coeff y • y
  refine
    ⟨coeff, terms, raw + x, hterms, hsupport, hkirch,
      (kirchhoffSubmodule G vertices).add_mem hkirch hx, hboundaryError, ?_, hproj⟩
  exact chain_add_self_add raw x

/-- Kernel form of the raw Kirchhoff representative theorem: the boundary correction lies in the
kernel of the selected-boundary erasure map, inside the same Kirchhoff submodule. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryKernel_error_decomposition_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {x : G.edgeSet → Color}
    (hx : x ∈ kirchhoffSubmodule G vertices) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (boundaryError : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈ kirchhoffSubmodule G vertices ∧
            boundaryError ∈
                kirchhoffSubmodule G vertices ⊓
                  LinearMap.ker
                    (boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
              (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                    (∑ y ∈ terms, coeff y • y) =
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  rcases
    exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_error_decomposition_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ vertices hboundary hx with
    ⟨coeff, terms, boundaryError, hterms, hsupport, hkirch, herrorKirch, herrorSupported,
      hdecomp, hproj⟩
  refine ⟨coeff, terms, boundaryError, hterms, hsupport, hkirch, ?_, hdecomp, hproj⟩
  constructor
  · exact herrorKirch
  · exact
      (boundaryZeroProjection_eq_zero_iff_mem_boundarySupportedSubmodule
        (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
        (x := boundaryError)).2 herrorSupported

/-- Image form of the corrected quotient bridge: after erasing selected-boundary coordinates, the
raw Kirchhoff submodule is already generated by raw Definition 4.8 generator combinations that
remain Kirchhoff at the selected vertices. -/
theorem map_boundaryZeroProjection_kirchhoffSubmodule_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    Submodule.map
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
        (kirchhoffSubmodule G vertices) =
      Submodule.map
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
        (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) := by
  apply le_antisymm
  · intro z hz
    rcases Submodule.mem_map.mp hz with ⟨x, hx, rfl⟩
    rcases
      exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_eq_boundaryZeroProjection_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        emb data C₀ hC₀ vertices hboundary hx with
      ⟨coeff, terms, hterms, hsupport, hkirch, hproj⟩
    let raw : G.edgeSet → Color := ∑ y ∈ terms, coeff y • y
    have hrawSpan : raw ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ := by
      have hrawSpan' :
          raw ∈ Submodule.span F2 (kempeClosureGeneratorFamily emb.faceBoundary C₀) :=
        (Submodule.mem_span_iff_exists_finset_subset
          (R := F2) (s := kempeClosureGeneratorFamily emb.faceBoundary C₀)
          (x := raw)).2
          ⟨coeff, terms, hterms, hsupport, rfl⟩
      simpa [kempeClosureGeneratorSubspace] using hrawSpan'
    refine ⟨raw, ⟨hrawSpan, hkirch⟩, hproj⟩
  · intro z hz
    rcases Submodule.mem_map.mp hz with ⟨x, hx, rfl⟩
    exact ⟨x, hx.2, rfl⟩

/-- First-isomorphism form of the corrected generator-side quotient bridge: the raw Kirchhoff
quotient by the selected-boundary kernel is linearly equivalent to the selected-boundary-erased
image of raw Definition 4.8 generator-span chains that are still Kirchhoff. -/
noncomputable def boundaryZeroProjectionKirchhoffQuotientEquivKempeKirchhoffImage_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    (kirchhoffSubmodule G vertices ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            (kirchhoffSubmodule G vertices))) ≃ₗ[F2]
      Submodule.map
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
        (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) :=
  (boundaryZeroProjectionKirchhoffQuotientEquivImage
      (G := G)
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) vertices).trans
    (LinearEquiv.ofEq _ _
      (map_boundaryZeroProjection_kirchhoffSubmodule_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        emb data C₀ hC₀ vertices hboundary))

theorem boundaryZeroProjectionKirchhoffQuotientEquivKempeKirchhoffImage_apply_mk_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    (x : kirchhoffSubmodule G vertices) :
    ((boundaryZeroProjectionKirchhoffQuotientEquivKempeKirchhoffImage_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        (G := G) emb data C₀ hC₀ vertices hboundary
        (Submodule.Quotient.mk x) :
        Submodule.map
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
          (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices)) :
        G.edgeSet → Color) =
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
        (x : G.edgeSet → Color) := by
  rw [
    boundaryZeroProjectionKirchhoffQuotientEquivKempeKirchhoffImage_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData]
  simp [boundaryZeroProjectionKirchhoffQuotientEquivImage_apply_mk]

/-- Target form of the corrected quotient bridge: the concrete boundary-zero Kirchhoff target is
the selected-boundary erasure of raw Definition 4.8 generator-span chains that already satisfy the
same Kirchhoff equations. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices =
      Submodule.map
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
        (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) := by
  rw [
    theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kirchhoffSubmodule_of_selectedBoundary_avoids_vertices
      (G := G) (emb := emb) (vertices := vertices) hboundary,
    map_boundaryZeroProjection_kirchhoffSubmodule_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ vertices hboundary]

/-- First-isomorphism form of the corrected source itself: the raw Definition 4.8
generator/Kirchhoff source modulo its restricted selected-boundary kernel is linearly equivalent to
the concrete boundary-zero Kirchhoff target. -/
noncomputable def boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    (↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices))) ≃ₗ[F2]
      theorem49BoundaryZeroKirchhoffSubspace emb vertices :=
  (boundaryZeroProjectionSubmoduleQuotientEquivImage
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
      (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices)).trans
    (LinearEquiv.ofEq _ _
      (theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        emb data C₀ hC₀ vertices hboundary).symm)

theorem boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_apply_mk_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    (x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices)) :
    ((boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        (G := G) emb data C₀ hC₀ vertices hboundary
        (Submodule.Quotient.mk x) :
        theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
        G.edgeSet → Color) =
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
        (x : G.edgeSet → Color) := by
  rw [
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData]
  simp [boundaryZeroProjectionSubmoduleQuotientEquivImage_apply_mk]

theorem boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_apply_mk_eq_zero_iff_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    (x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices)) :
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        (G := G) emb data C₀ hC₀ vertices hboundary (Submodule.Quotient.mk x) = 0 ↔
      (x : G.edgeSet → Color) ∈
        boundarySupportedSubmodule
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
  let e :=
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) emb data C₀ hC₀ vertices hboundary
  rw [← map_zero e]
  rw [e.injective.eq_iff]
  exact selectedBoundaryProjectionKempeKirchhoffQuotient_mk_eq_zero_iff
    (emb := emb) (C₀ := C₀) (vertices := vertices) (x := x)

/-- Substantive `W₀(H)` characterization using the corrected quotient route: an ambient edge-chain
is in the concrete boundary-zero Kirchhoff target exactly when it is the image of a class in the
raw Definition 4.8 generator/Kirchhoff source quotient. -/
theorem mem_theorem49BoundaryZeroKirchhoffSubspace_iff_exists_boundaryZeroProjectionKempeKirchhoffQuotientClass_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {z : G.edgeSet → Color} :
    z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices ↔
      ∃ q : (↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) ⧸
        LinearMap.ker
          ((boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
              (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices))),
        ((boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
            emb data C₀ hC₀ vertices hboundary q :
            theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
            G.edgeSet → Color) = z := by
  let e :=
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) emb data C₀ hC₀ vertices hboundary
  constructor
  · intro hz
    let zW : theorem49BoundaryZeroKirchhoffSubspace emb vertices := ⟨z, hz⟩
    refine ⟨e.symm zW, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply zW)
  · rintro ⟨q, hq⟩
    rw [← hq]
    exact (e q).property

/-- Pull the Theorem 4.9 annihilator endpoint back to the corrected raw source quotient:
a quotient class maps to a concrete `W₀(H)` annihilator exactly when the class is zero. -/
theorem boundaryZeroProjectionKempeKirchhoffQuotientClass_eq_zero_iff_annihilatesKempeClosureGeneratorFamily_image_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    (q : (↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices)))) :
    q = 0 ↔
      AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀
        ((boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
            (G := G) emb data C₀ hC₀ vertices hboundary q :
            theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
            G.edgeSet → Color) := by
  let φ :=
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) emb data C₀ hC₀ vertices hboundary
  change q = 0 ↔
    AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀
      ((φ q : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
        G.edgeSet → Color)
  constructor
  · intro hq
    rw [hq]
    have hzero :
        ((φ 0 : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
          G.edgeSet → Color) = 0 := by
      simp [φ]
    intro C _hC f a b _hab
    rw [hzero]
    simp [chainDot]
  · intro hAnnih
    have hzeroEdges :
        ∀ edge : G.edgeSet,
          ((φ q : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
            G.edgeSet → Color) edge = 0 :=
      boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        emb data C₀ hC₀
        ((φ q : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
          G.edgeSet → Color)
        (boundaryZero_of_mem_theorem49BoundaryZeroKirchhoffSubspace
          (φ q).property)
        hAnnih
    have hφq : φ q = 0 := by
      apply Subtype.ext
      funext edge
      exact hzeroEdges edge
    have hφq0 : φ q = φ 0 := by
      simpa using hφq
    exact φ.injective hφq0

/-- Orthogonality-facing form of the corrected quotient route: a source quotient class maps into
the projected-generator orthogonal complement exactly when the class is zero. -/
theorem boundaryZeroProjectionKempeKirchhoffQuotientClass_eq_zero_iff_image_mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    (q : (↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices)))) :
    q = 0 ↔
      ((boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
          (G := G) emb data C₀ hC₀ vertices hboundary q :
          theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
          G.edgeSet → Color) ∈
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedKempeClosureGeneratorSubspace emb C₀) := by
  let φ :=
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) emb data C₀ hC₀ vertices hboundary
  change q = 0 ↔
      ((φ q : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
        G.edgeSet → Color) ∈
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedKempeClosureGeneratorSubspace emb C₀)
  constructor
  · intro hq
    rw [hq]
    have hzero :
        ((φ 0 : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
          G.edgeSet → Color) = 0 := by
      simp [φ]
    intro x _hx
    rw [hzero]
    exact (chainDotBilinForm G.edgeSet x).map_zero
  · intro hOrth
    have hboundaryZero :
        ((φ q : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
          G.edgeSet → Color) ∈ planarBoundaryZeroSubmodule emb :=
      theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
        emb vertices (φ q).property
    have hAnnih :
        AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀
          ((φ q : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
            G.edgeSet → Color) :=
      (mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_iff_annihilatesKempeClosureGeneratorFamily
        (G := G) (emb := emb) (C₀ := C₀)
        (z := ((φ q : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
          G.edgeSet → Color))
        hboundaryZero).1 hOrth
    exact
      (boundaryZeroProjectionKempeKirchhoffQuotientClass_eq_zero_iff_annihilatesKempeClosureGeneratorFamily_image_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
        (vertices := vertices) hboundary q).2 hAnnih

/-- Concrete `W₀(H)` linear-duality consequence of the corrected quotient route: no nonzero
boundary-zero Kirchhoff target chain is orthogonal to the projected Definition 4.8 generator
span once the interior-dual annihilator route is available. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices ⊓
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedKempeClosureGeneratorSubspace emb C₀) =
      ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  let φ :=
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) emb data C₀ hC₀ vertices hboundary
  let zW : theorem49BoundaryZeroKirchhoffSubspace emb vertices := ⟨z, hz.1⟩
  let q := φ.symm zW
  have hqOrth :
      ((φ q : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
        G.edgeSet → Color) ∈
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedKempeClosureGeneratorSubspace emb C₀) := by
    have hφq : (φ q : theorem49BoundaryZeroKirchhoffSubspace emb vertices) = zW :=
      φ.apply_symm_apply zW
    simpa [zW] using hφq ▸ hz.2
  have hqZero : q = 0 :=
    (boundaryZeroProjectionKempeKirchhoffQuotientClass_eq_zero_iff_image_mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := vertices) hboundary q).2 hqOrth
  have hzW : zW = 0 := by
    calc
      zW = φ (φ.symm zW) := (φ.apply_symm_apply zW).symm
      _ = φ q := rfl
      _ = φ 0 := by rw [hqZero]
      _ = 0 := map_zero φ
  exact congrArg Subtype.val hzW

/-- Detection form of the corrected quotient route: every nonzero source quotient class has a
projected Definition 4.8 generator-span chain pairing nontrivially with its concrete `W₀(H)`
image. -/
theorem exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_boundaryZeroProjectionKempeKirchhoffQuotientClass_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {q : (↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices)))}
    (hq : q ≠ 0) :
    ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p
        ((boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
            (G := G) emb data C₀ hC₀ vertices hboundary q :
            theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
            G.edgeSet → Color) ≠ 0 := by
  classical
  let φ :=
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) emb data C₀ hC₀ vertices hboundary
  by_contra hnone
  have hOrth :
      ((φ q : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
        G.edgeSet → Color) ∈
        (chainDotBilinForm G.edgeSet).orthogonal
          (projectedKempeClosureGeneratorSubspace emb C₀) := by
    intro p hp
    by_contra hdot
    exact hnone ⟨p, hp, hdot⟩
  exact hq
    ((boundaryZeroProjectionKempeKirchhoffQuotientClass_eq_zero_iff_image_mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := vertices) hboundary q).2 hOrth)

/-- Concrete `W₀(H)` detector form of the corrected quotient route: every nonzero boundary-zero
Kirchhoff target chain pairs nontrivially with some projected Definition 4.8 generator-span
chain. -/
theorem exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {z : theorem49BoundaryZeroKirchhoffSubspace emb vertices}
    (hz : z ≠ 0) :
    ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  let φ :=
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) emb data C₀ hC₀ vertices hboundary
  let q := φ.symm z
  have hq : q ≠ 0 := by
    intro hq0
    have hz0 : z = 0 := by
      calc
        z = φ (φ.symm z) := (φ.apply_symm_apply z).symm
        _ = φ q := rfl
        _ = φ 0 := by rw [hq0]
        _ = 0 := map_zero φ
    exact hz hz0
  rcases
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_boundaryZeroProjectionKempeKirchhoffQuotientClass_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := vertices) hboundary hq with
    ⟨p, hp, hpair⟩
  have hφq :
      ((φ q : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
        G.edgeSet → Color) = (z : G.edgeSet → Color) :=
    congrArg Subtype.val (φ.apply_symm_apply z)
  have hpair' :
      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
    rw [← hφq]
    exact hpair
  exact ⟨p, hp, hpair'⟩

/-- Pointwise `W₀(H)` orthogonality characterization against the projected Definition 4.8
generator span. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {z : theorem49BoundaryZeroKirchhoffSubspace emb vertices} :
    (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
      z = 0 := by
  constructor
  · intro hzero
    by_contra hz
    rcases
      exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
        (vertices := vertices) hboundary hz with
      ⟨p, hp, hpair⟩
    exact hpair (hzero p hp)
  · intro hz p _hp
    rw [hz]
    exact (chainDotBilinForm G.edgeSet p).map_zero

/-- The concrete pairing map from `W₀(H)` into the dual of the projected Definition 4.8
generator span.  It sends a boundary-zero Kirchhoff chain to its chain-dot functional on the
projected generator span. -/
noncomputable def theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color) (vertices : Finset V) :
    theorem49BoundaryZeroKirchhoffSubspace emb vertices →ₗ[F2]
      (projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2) where
  toFun z :=
    { toFun := fun p =>
        chainDotBilinForm G.edgeSet (p : G.edgeSet → Color) (z : G.edgeSet → Color)
      map_add' := by
        intro p q
        change
          chainDotBilinForm G.edgeSet
              ((p + q : projectedKempeClosureGeneratorSubspace emb C₀) : G.edgeSet → Color)
              (z : G.edgeSet → Color) =
            chainDotBilinForm G.edgeSet (p : G.edgeSet → Color) (z : G.edgeSet → Color) +
              chainDotBilinForm G.edgeSet (q : G.edgeSet → Color) (z : G.edgeSet → Color)
        exact congrArg (fun f : (G.edgeSet → Color) →ₗ[F2] F2 =>
            f (z : G.edgeSet → Color))
          ((chainDotBilinForm G.edgeSet).map_add
            (p : G.edgeSet → Color) (q : G.edgeSet → Color))
      map_smul' := by
        intro a p
        change
          chainDotBilinForm G.edgeSet
              ((a • p : projectedKempeClosureGeneratorSubspace emb C₀) : G.edgeSet → Color)
              (z : G.edgeSet → Color) =
            a • chainDotBilinForm G.edgeSet (p : G.edgeSet → Color) (z : G.edgeSet → Color)
        exact congrArg (fun f : (G.edgeSet → Color) →ₗ[F2] F2 =>
            f (z : G.edgeSet → Color))
          ((chainDotBilinForm G.edgeSet).map_smul a (p : G.edgeSet → Color)) }
  map_add' := by
    intro z w
    ext p
    change
      chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)
          ((z + w : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
            G.edgeSet → Color) =
        chainDotBilinForm G.edgeSet (p : G.edgeSet → Color) (z : G.edgeSet → Color) +
          chainDotBilinForm G.edgeSet (p : G.edgeSet → Color) (w : G.edgeSet → Color)
    simpa using
      ((chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)).map_add
        (z : G.edgeSet → Color) (w : G.edgeSet → Color))
  map_smul' := by
    intro a z
    ext p
    change
      chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)
          ((a • z : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
            G.edgeSet → Color) =
        a • chainDotBilinForm G.edgeSet (p : G.edgeSet → Color) (z : G.edgeSet → Color)
    exact
      ((chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)).map_smul a
        (z : G.edgeSet → Color))

/-- The quotient-derived `W₀(H)` detector says that the concrete pairing map into the projected
generator-span dual has trivial kernel. -/
theorem ker_theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap_eq_bot_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    LinearMap.ker
        (theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
          (G := G) emb C₀ vertices) =
      ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  exact
    (theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := vertices) hboundary (z := z)).1
      (by
        intro p hp
        let p' : projectedKempeClosureGeneratorSubspace emb C₀ := ⟨p, hp⟩
        have hmap :
            theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
                (G := G) emb C₀ vertices z = 0 := hz
        have hcoord := congrArg
          (fun f : projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2 => f p') hmap
        simpa [theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap, p'] using hcoord)

/-- Finite-dimensional consequence of the concrete pairing injection: `W₀(H)` has dimension at
most the projected Definition 4.8 generator span. -/
theorem finrank_theorem49BoundaryZeroKirchhoffSubspace_le_finrank_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    Module.finrank F2 (theorem49BoundaryZeroKirchhoffSubspace emb vertices) ≤
      Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀) := by
  let L :=
    theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
      (G := G) emb C₀ vertices
  have hker : LinearMap.ker L = ⊥ :=
    ker_theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap_eq_bot_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := vertices) hboundary
  have hinj : Function.Injective L := (LinearMap.ker_eq_bot).1 hker
  have hleDual :
      Module.finrank F2 (theorem49BoundaryZeroKirchhoffSubspace emb vertices) ≤
        Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2) :=
    LinearMap.finrank_le_finrank_of_injective (f := L) hinj
  simpa [L, Module.Dual] using
    hleDual.trans_eq
      (Subspace.dual_finrank_eq
        (K := F2) (V := projectedKempeClosureGeneratorSubspace emb C₀))

theorem boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_symm_eq_mk_of_projection_eq
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb}
    {C₀ : G.EdgeColoring Color} {hC₀ : IsTaitEdgeColoring G C₀}
    {vertices : Finset V}
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {z : theorem49BoundaryZeroKirchhoffSubspace emb vertices}
    (x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices))
    (hx : boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
        (x : G.edgeSet → Color) = (z : G.edgeSet → Color)) :
    (boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        (G := G) emb data C₀ hC₀ vertices hboundary).symm z =
      Submodule.Quotient.mk x := by
  let e :=
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) emb data C₀ hC₀ vertices hboundary
  apply e.injective
  apply Subtype.ext
  have happ :=
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_apply_mk_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := vertices) hboundary x
  simpa [e, hx] using happ.symm

/-- Operational preimage form of the target quotient bridge: every concrete boundary-zero
Kirchhoff target chain has a selected-boundary projection preimage lying simultaneously in the raw
Definition 4.8 generator span and in the raw Kirchhoff submodule. -/
theorem exists_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    {z : G.edgeSet → Color}
    (hz : z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices,
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  have htarget :=
    theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ vertices hboundary
  rw [htarget] at hz
  exact Submodule.mem_map.mp hz

/-- Quotient-representative form of the target bridge: every concrete boundary-zero Kirchhoff
target chain is the image of an explicit class in the corrected raw generator/Kirchhoff source
quotient. -/
theorem exists_boundaryZeroProjectionKempeKirchhoffQuotientRepresentative_eq_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    (z : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices),
      boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
        emb data C₀ hC₀ vertices hboundary (Submodule.Quotient.mk x) = z := by
  rcases
    exists_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ vertices hboundary z.property with
    ⟨y, hy, hproj⟩
  let x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) :=
    ⟨y, hy⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  have happ :=
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_apply_mk_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := vertices) hboundary x
  exact by
    simpa [x] using happ.trans hproj

/-- Inverse-equivalence representative form of the target bridge: the inverse image of every
concrete boundary-zero Kirchhoff target chain has a representative in the corrected raw
generator/Kirchhoff source. -/
theorem exists_boundaryZeroProjectionKempeKirchhoffQuotientRepresentative_symm_eq_mk_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (vertices : Finset V)
    (hboundary : ∀ v ∈ vertices,
      ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V))
    (z : theorem49BoundaryZeroKirchhoffSubspace emb vertices) :
    ∃ x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices),
      (boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
          (G := G) emb data C₀ hC₀ vertices hboundary).symm z =
        Submodule.Quotient.mk x := by
  rcases
    exists_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ vertices hboundary z.property with
    ⟨y, hy, hproj⟩
  let x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ kirchhoffSubmodule G vertices) :=
    ⟨y, hy⟩
  exact ⟨x,
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_symm_eq_mk_of_projection_eq
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := vertices) hboundary x (by simpa [x] using hproj)⟩

/-- Graph-level target identity for the current route: on an admitted boundary-rooted
interior-dual embedding, if the selected target vertices avoid the selected boundary support, then
the concrete boundary-zero Kirchhoff target is the boundary erasure image of the raw Kirchhoff
submodule. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kirchhoffSubmodule_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) =
          Submodule.map
            (boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
            (kirchhoffSubmodule G (verticesOf emb data)) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kirchhoffSubmodule_of_selectedBoundary_avoids_vertices
      (G := G) (emb := emb) (vertices := verticesOf emb data) (hboundary emb data)⟩

/-- Graph-level local quotient relation: on a witnessing boundary-rooted interior-dual embedding,
selected-boundary projection identifies exactly those raw Kirchhoff chains whose sum lies in the
Kirchhoff submodule and is supported on the selected boundary. -/
theorem exists_selectedBoundaryProjection_eq_iff_add_mem_kirchhoffSubmodule_inf_boundarySupportedSubmodule_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {x y : G.edgeSet → Color},
          x ∈ kirchhoffSubmodule G (verticesOf emb data) →
          y ∈ kirchhoffSubmodule G (verticesOf emb data) →
            (boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y =
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x ↔
              y + x ∈
                kirchhoffSubmodule G (verticesOf emb data) ⊓
                  boundarySupportedSubmodule
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro x y hx hy
  exact
    selectedBoundaryProjection_eq_iff_add_mem_kirchhoffSubmodule_inf_boundarySupportedSubmodule
      (emb := emb) (vertices := verticesOf emb data) hx hy

/-- Graph-level local quotient relation for the corrected Definition 4.8 source itself: on a
witnessing boundary-rooted interior-dual embedding, selected-boundary projection identifies exactly
those raw generator/Kirchhoff chains whose sum is again in that source and is supported on the
selected boundary. -/
theorem exists_selectedBoundaryProjection_eq_iff_add_mem_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_inf_boundarySupportedSubmodule_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {x y : G.edgeSet → Color},
          x ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G (verticesOf emb data) →
          y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G (verticesOf emb data) →
            (boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y =
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x ↔
              y + x ∈
                (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                    kirchhoffSubmodule G (verticesOf emb data)) ⊓
                  boundarySupportedSubmodule
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro x y hx hy
  exact
    selectedBoundaryProjection_eq_iff_add_mem_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_inf_boundarySupportedSubmodule
      (emb := emb) (C₀ := C₀) (vertices := verticesOf emb data) hx hy

/-- Graph-level representative equality criterion for the corrected Definition 4.8 source
quotient: two raw generator/Kirchhoff representatives define the same quotient class exactly when
their selected-boundary-erased chains are equal. -/
theorem exists_selectedBoundaryProjectionKempeKirchhoffQuotient_mk_eq_mk_iff_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {x y : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G (verticesOf emb data))},
          ((Submodule.Quotient.mk x :
              ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                  kirchhoffSubmodule G (verticesOf emb data)) ⧸
                LinearMap.ker
                  ((boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                      (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                        kirchhoffSubmodule G (verticesOf emb data)))) =
              Submodule.Quotient.mk y ↔
            boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (x : G.edgeSet → Color) =
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (y : G.edgeSet → Color)) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun {x y} =>
    selectedBoundaryProjectionKempeKirchhoffQuotient_mk_eq_mk_iff
      (emb := emb) (C₀ := C₀) (vertices := verticesOf emb data)
      (x := x) (y := y)⟩

/-- Graph-level zero-class criterion for the corrected Definition 4.8 source quotient: a raw
generator/Kirchhoff representative maps to the zero quotient class exactly when it is supported on
the selected boundary. -/
theorem exists_selectedBoundaryProjectionKempeKirchhoffQuotient_mk_eq_zero_iff_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G (verticesOf emb data))},
          ((Submodule.Quotient.mk x :
              ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                  kirchhoffSubmodule G (verticesOf emb data)) ⧸
                LinearMap.ker
                  ((boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                      (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                        kirchhoffSubmodule G (verticesOf emb data)))) = 0 ↔
            (x : G.edgeSet → Color) ∈
              boundarySupportedSubmodule
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun {x} =>
    selectedBoundaryProjectionKempeKirchhoffQuotient_mk_eq_zero_iff
      (emb := emb) (C₀ := C₀) (vertices := verticesOf emb data) (x := x)⟩

/-- Graph-level first-isomorphism witness for the raw Kirchhoff quotient by the selected-boundary
kernel on an admitted boundary-rooted interior-dual embedding. -/
theorem exists_selectedBoundaryProjectionKirchhoffQuotientEquivImage_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        Nonempty
          ((kirchhoffSubmodule G (verticesOf emb data) ⧸
            LinearMap.ker
              ((boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kirchhoffSubmodule G (verticesOf emb data)))) ≃ₗ[F2]
            Submodule.map
              (boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
              (kirchhoffSubmodule G (verticesOf emb data))) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    ⟨boundaryZeroProjectionKirchhoffQuotientEquivImage
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
      (verticesOf emb data)⟩⟩

/-- Graph-level first-isomorphism witness landing directly in the concrete boundary-zero Kirchhoff
target, under the selected-boundary/interior-vertex disjointness side condition. -/
theorem exists_selectedBoundaryProjectionKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} [Fintype G.edgeSet]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        Nonempty
          ((kirchhoffSubmodule G (verticesOf emb data) ⧸
            LinearMap.ker
              ((boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kirchhoffSubmodule G (verticesOf emb data)))) ≃ₗ[F2]
            theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data)) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    ⟨selectedBoundaryProjectionKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace
      emb (verticesOf emb data) (hboundary emb data)⟩⟩

/-- Graph-level projected-source spanning theorem from the current interior-dual route: if the
graph admits the boundary-rooted interior-dual data, then on some witnessing embedding the
selected-boundary-erased Definition 4.8 generator span is exactly the boundary-zero subspace. -/
theorem exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        projectedKempeClosureGeneratorSubspace emb C₀ = planarBoundaryZeroSubmodule emb := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀⟩

/-- Graph-level explicit generator-family form of the projected-source spanning theorem. -/
theorem exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
          planarBoundaryZeroSubmodule emb := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀⟩

/-- Graph-level route characterization of the concrete target: for a witnessing embedding, `W0`
is the Kirchhoff subspace intersected with the selected-boundary-erased Definition 4.8 generator
span. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) =
          kirchhoffSubmodule G (verticesOf emb data) ⊓
            projectedKempeClosureGeneratorSubspace emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level explicit-family characterization of the concrete target: for a witnessing
embedding, `W0` is the Kirchhoff subspace intersected with the span of the projected Definition 4.8
generator family. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_span_projectedKempeClosureGeneratorFamily_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) =
          kirchhoffSubmodule G (verticesOf emb data) ⊓
            Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level finite-combination form of the corrected projected-source Theorem 4.9 statement. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
                coeff.support ⊆ terms ∧
                  ∑ y ∈ terms, coeff y • y = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) hz

/-- Graph-level route-facing inclusion for a chosen target vertex set on the witnessing embedding:
the concrete boundary-zero Kirchhoff target lies in the corrected projected generator span. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ≤
          projectedKempeClosureGeneratorSubspace emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level height-ordered projected-source spanning theorem: if the graph admits a
same-embedding height-ordered witness-cover surface, then the boundary-erased Definition 4.8
generator span is the full selected-boundary-zero subspace on some witnessing embedding. -/
theorem exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        projectedKempeClosureGeneratorSubspace emb C₀ = planarBoundaryZeroSubmodule emb := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀⟩

/-- Graph-level finite-collar projected-source spanning theorem. -/
theorem exists_projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        projectedKempeClosureGeneratorSubspace emb C₀ = planarBoundaryZeroSubmodule emb := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀⟩

/-- Graph-level explicit-family height-ordered projected-source spanning theorem. -/
theorem exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
          planarBoundaryZeroSubmodule emb := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀⟩

/-- Graph-level explicit-family finite-collar projected-source spanning theorem. -/
theorem exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
          planarBoundaryZeroSubmodule emb := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀⟩

/-- Graph-level local explicit-remainder projected-source spanning theorem. -/
theorem exists_span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) =
          planarBoundaryZeroSubmodule emb := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀⟩

/-- Graph-level height-ordered characterization of the concrete boundary-zero Kirchhoff target. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) =
          kirchhoffSubmodule G (verticesOf emb data) ⊓
            projectedKempeClosureGeneratorSubspace emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level finite-collar characterization of the concrete boundary-zero Kirchhoff target. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) =
          kirchhoffSubmodule G (verticesOf emb data) ⊓
            projectedKempeClosureGeneratorSubspace emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_projectedKempeClosureGeneratorSubspace_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level height-ordered finite-combination form of the corrected projected-source
Theorem 4.9 statement. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
                coeff.support ⊆ terms ∧
                  ∑ y ∈ terms, coeff y • y = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) hz

/-- Graph-level finite-collar finite-combination form of the corrected projected-source
Theorem 4.9 statement. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
                coeff.support ⊆ terms ∧
                  ∑ y ∈ terms, coeff y • y = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) hz

/-- Graph-level local explicit-remainder finite-combination form of the corrected
projected-source Theorem 4.9 statement. -/
theorem exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆ projectedKempeClosureGeneratorFamily emb C₀ ∧
                coeff.support ⊆ terms ∧
                  ∑ y ∈ terms, coeff y • y = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) hz

/-- Graph-level height-ordered explicit-family characterization of the concrete boundary-zero
Kirchhoff target. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_span_projectedKempeClosureGeneratorFamily_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) =
          kirchhoffSubmodule G (verticesOf emb data) ⊓
            Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level finite-collar explicit-family characterization of the concrete boundary-zero
Kirchhoff target. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_span_projectedKempeClosureGeneratorFamily_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) =
          kirchhoffSubmodule G (verticesOf emb data) ⊓
            Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_eq_kirchhoffSubmodule_inf_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level height-ordered route-facing inclusion into the projected Definition 4.8 span. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ≤
          projectedKempeClosureGeneratorSubspace emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level finite-collar route-facing inclusion into the projected Definition 4.8 span. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ≤
          projectedKempeClosureGeneratorSubspace emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level height-ordered route-facing inclusion into the explicit projected generator
family span. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_le_span_projectedKempeClosureGeneratorFamily_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ≤
          Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_le_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level finite-collar route-facing inclusion into the explicit projected generator
family span. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_le_span_projectedKempeClosureGeneratorFamily_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ≤
          Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_le_span_projectedKempeClosureGeneratorFamily_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level height-ordered projected-source separation theorem.  The concrete boundary-zero
Kirchhoff target has no nonzero chain orthogonal to the projected Definition 4.8 generator span
on the witnessing embedding. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C₀) =
          ⊥ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level finite-collar projected-source separation theorem. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C₀) =
          ⊥ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level height-ordered detector theorem for nonzero concrete `W₀(H)` chains. -/
theorem exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun z hz =>
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) hz⟩

/-- Graph-level finite-collar detector theorem for nonzero concrete `W₀(H)` chains. -/
theorem exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun z hz =>
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) hz⟩

/-- Graph-level height-ordered pointwise orthogonality characterization against the projected
Definition 4.8 generator span. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun z =>
    theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level finite-collar pointwise orthogonality characterization against the projected
Definition 4.8 generator span. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun z =>
    theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data)⟩

/-- Graph-level height-ordered raw-subspace preimage form of the corrected Theorem 4.9 source
statement. -/
theorem exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) hz

/-- Graph-level finite-collar raw-subspace preimage form of the corrected Theorem 4.9 source
statement. -/
theorem exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) hz

/-- Graph-level local explicit-remainder raw-subspace preimage form of the corrected Theorem 4.9
source statement. -/
theorem exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) hz

/-- Graph-level height-ordered raw finite-generator form of the corrected Theorem 4.9 source
statement. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryHeightOrderedFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryHeightOrderedFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) hz

/-- Graph-level finite-collar raw finite-generator form of the corrected Theorem 4.9 source
statement. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) hz

/-- Graph-level local explicit-remainder raw finite-generator form of the corrected Theorem 4.9
source statement. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) hz

/-- Graph-level local explicit-remainder raw finite-generator witness with the raw Kirchhoff
equations retained, assuming the chosen target vertices avoid the selected boundary support on the
witnessing embedding. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_and_mem_kirchhoffSubmodule_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  (∑ y ∈ terms, coeff y • y) ∈
                      kirchhoffSubmodule G (verticesOf emb data) ∧
                    boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                        (∑ y ∈ terms, coeff y • y) = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_and_mem_kirchhoffSubmodule_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) hz

/-- Graph-level local explicit-remainder quotient-style raw Kirchhoff form of the corrected
Theorem 4.9 source statement. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_eq_boundaryZeroProjection_of_mem_kirchhoffSubmodule_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {x : G.edgeSet → Color},
          x ∈ kirchhoffSubmodule G (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  (∑ y ∈ terms, coeff y • y) ∈
                      kirchhoffSubmodule G (verticesOf emb data) ∧
                    boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                        (∑ y ∈ terms, coeff y • y) =
                      boundaryZeroProjection
                        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro x hx
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_eq_boundaryZeroProjection_of_mem_kirchhoffSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) hx

/-- Graph-level local explicit-remainder boundary-kernel form of the raw Kirchhoff representative
theorem. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_difference_of_mem_kirchhoffSubmodule_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {x : G.edgeSet → Color},
          x ∈ kirchhoffSubmodule G (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  (∑ y ∈ terms, coeff y • y) ∈
                      kirchhoffSubmodule G (verticesOf emb data) ∧
                    (∑ y ∈ terms, coeff y • y) + x ∈
                        boundarySupportedSubmodule
                          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                      boundaryZeroProjection
                        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                          (∑ y ∈ terms, coeff y • y) =
                        boundaryZeroProjection
                          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro x hx
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_difference_of_mem_kirchhoffSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) hx

/-- Graph-level local explicit-remainder decomposition form of the raw Kirchhoff representative
theorem. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_error_decomposition_of_mem_kirchhoffSubmodule_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {x : G.edgeSet → Color},
          x ∈ kirchhoffSubmodule G (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
                (boundaryError : G.edgeSet → Color),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  (∑ y ∈ terms, coeff y • y) ∈
                      kirchhoffSubmodule G (verticesOf emb data) ∧
                    boundaryError ∈ kirchhoffSubmodule G (verticesOf emb data) ∧
                      boundaryError ∈
                          boundarySupportedSubmodule
                            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                        (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                          boundaryZeroProjection
                            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                              (∑ y ∈ terms, coeff y • y) =
                            boundaryZeroProjection
                              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                                x := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro x hx
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_error_decomposition_of_mem_kirchhoffSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) hx

/-- Graph-level local explicit-remainder kernel-decomposition form of the raw Kirchhoff
representative theorem. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryKernel_error_decomposition_of_mem_kirchhoffSubmodule_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb,
        ∀ {x : G.edgeSet → Color},
          x ∈ kirchhoffSubmodule G (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
                (boundaryError : G.edgeSet → Color),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  (∑ y ∈ terms, coeff y • y) ∈
                      kirchhoffSubmodule G (verticesOf emb data) ∧
                    boundaryError ∈
                        kirchhoffSubmodule G (verticesOf emb data) ⊓
                          LinearMap.ker
                            (boundaryZeroProjection
                              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
                      (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                        boundaryZeroProjection
                          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                            (∑ y ∈ terms, coeff y • y) =
                          boundaryZeroProjection
                            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                              x := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro x hx
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryKernel_error_decomposition_of_mem_kirchhoffSubmodule_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) hx

/-- Graph-level operational form of the corrected Theorem 4.9 source statement: on a witnessing
embedding, every chain in the chosen boundary-zero Kirchhoff target has a raw Definition 4.8
generator-span preimage whose selected-boundary projection is the chain. -/
theorem exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀,
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorSubspace_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) hz

/-- Graph-level finite raw-generator form of the corrected Theorem 4.9 source statement. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) hz

/-- Graph-level finite raw-generator witness with the raw Kirchhoff equations retained, assuming
the chosen target vertices avoid the selected boundary support on the witnessing embedding. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_and_mem_kirchhoffSubmodule_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  (∑ y ∈ terms, coeff y • y) ∈
                      kirchhoffSubmodule G (verticesOf emb data) ∧
                    boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                        (∑ y ∈ terms, coeff y • y) = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_and_mem_kirchhoffSubmodule_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) hz

/-- Graph-level quotient-style raw Kirchhoff form of the corrected Theorem 4.9 source statement. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_eq_boundaryZeroProjection_of_mem_kirchhoffSubmodule_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {x : G.edgeSet → Color},
          x ∈ kirchhoffSubmodule G (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  (∑ y ∈ terms, coeff y • y) ∈
                      kirchhoffSubmodule G (verticesOf emb data) ∧
                    boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                        (∑ y ∈ terms, coeff y • y) =
                      boundaryZeroProjection
                        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro x hx
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_eq_boundaryZeroProjection_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) hx

/-- Graph-level boundary-kernel form of the raw Kirchhoff representative theorem. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_difference_of_mem_kirchhoffSubmodule_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {x : G.edgeSet → Color},
          x ∈ kirchhoffSubmodule G (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  (∑ y ∈ terms, coeff y • y) ∈
                      kirchhoffSubmodule G (verticesOf emb data) ∧
                    (∑ y ∈ terms, coeff y • y) + x ∈
                        boundarySupportedSubmodule
                          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                      boundaryZeroProjection
                        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                          (∑ y ∈ terms, coeff y • y) =
                        boundaryZeroProjection
                          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro x hx
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_difference_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) hx

/-- Graph-level decomposition form of the raw Kirchhoff representative theorem. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_error_decomposition_of_mem_kirchhoffSubmodule_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {x : G.edgeSet → Color},
          x ∈ kirchhoffSubmodule G (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
                (boundaryError : G.edgeSet → Color),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  (∑ y ∈ terms, coeff y • y) ∈
                      kirchhoffSubmodule G (verticesOf emb data) ∧
                    boundaryError ∈ kirchhoffSubmodule G (verticesOf emb data) ∧
                      boundaryError ∈
                          boundarySupportedSubmodule
                            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
                        (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                          boundaryZeroProjection
                            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                              (∑ y ∈ terms, coeff y • y) =
                            boundaryZeroProjection
                              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                                x := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro x hx
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundarySupported_error_decomposition_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) hx

/-- Graph-level kernel-decomposition form of the raw Kirchhoff representative theorem. -/
theorem exists_kempeClosureGeneratorFamily_finset_sum_boundaryKernel_error_decomposition_of_mem_kirchhoffSubmodule_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {x : G.edgeSet → Color},
          x ∈ kirchhoffSubmodule G (verticesOf emb data) →
            ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
                (boundaryError : G.edgeSet → Color),
              (terms : Set (G.edgeSet → Color)) ⊆
                  kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff.support ⊆ terms ∧
                  (∑ y ∈ terms, coeff y • y) ∈
                      kirchhoffSubmodule G (verticesOf emb data) ∧
                    boundaryError ∈
                        kirchhoffSubmodule G (verticesOf emb data) ⊓
                          LinearMap.ker
                            (boundaryZeroProjection
                              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
                      (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                        boundaryZeroProjection
                          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                            (∑ y ∈ terms, coeff y • y) =
                          boundaryZeroProjection
                            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                              x := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro x hx
  exact
    exists_kempeClosureGeneratorFamily_finset_sum_boundaryKernel_error_decomposition_of_mem_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) hx

/-- Graph-level image form of the corrected quotient bridge. -/
theorem exists_map_boundaryZeroProjection_kirchhoffSubmodule_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        Submodule.map
            (boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
            (kirchhoffSubmodule G (verticesOf emb data)) =
          Submodule.map
            (boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
            (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G (verticesOf emb data)) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    map_boundaryZeroProjection_kirchhoffSubmodule_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data)⟩

/-- Graph-level first-isomorphism form of the corrected generator-side quotient bridge. -/
theorem exists_boundaryZeroProjectionKirchhoffQuotientEquivKempeKirchhoffImage_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        Nonempty
          ((kirchhoffSubmodule G (verticesOf emb data) ⧸
            LinearMap.ker
              ((boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kirchhoffSubmodule G (verticesOf emb data)))) ≃ₗ[F2]
            Submodule.map
              (boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
              (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                kirchhoffSubmodule G (verticesOf emb data))) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    ⟨boundaryZeroProjectionKirchhoffQuotientEquivKempeKirchhoffImage_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data)⟩⟩

/-- Graph-level target form of the corrected quotient bridge. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) =
          Submodule.map
            (boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
            (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G (verticesOf emb data)) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_eq_map_boundaryZeroProjection_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data)⟩

/-- Graph-level first-isomorphism form of the corrected source quotient landing in the concrete
boundary-zero Kirchhoff target. -/
theorem exists_boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        Nonempty
          ((↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G (verticesOf emb data)) ⧸
            LinearMap.ker
              ((boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                  kirchhoffSubmodule G (verticesOf emb data)))) ≃ₗ[F2]
            theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data)) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    ⟨boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data)⟩⟩

/-- Graph-level target-zero criterion for the corrected source quotient equivalence. -/
theorem exists_boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_apply_mk_eq_zero_iff_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G (verticesOf emb data)),
          (boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
              emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data)
                (Submodule.Quotient.mk x) = 0 ↔
            (x : G.edgeSet → Color) ∈
              boundarySupportedSubmodule
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun x =>
    boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_apply_mk_eq_zero_iff_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := verticesOf emb data) (hboundary emb data) x⟩

/-- Graph-level `W₀(H)` characterization using the corrected quotient route. -/
theorem exists_mem_theorem49BoundaryZeroKirchhoffSubspace_iff_exists_boundaryZeroProjectionKempeKirchhoffQuotientClass_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ↔
            ∃ q : (↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                kirchhoffSubmodule G (verticesOf emb data)) ⧸
              LinearMap.ker
                ((boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                    (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                      kirchhoffSubmodule G (verticesOf emb data)))),
              ((boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
                  emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) q :
                  theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data)) :
                  G.edgeSet → Color) = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun {z} =>
    mem_theorem49BoundaryZeroKirchhoffSubspace_iff_exists_boundaryZeroProjectionKempeKirchhoffQuotientClass_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data)⟩

/-- Graph-level quotient-pulled annihilator criterion for the corrected `W₀(H)` route. -/
theorem exists_boundaryZeroProjectionKempeKirchhoffQuotientClass_eq_zero_iff_annihilatesKempeClosureGeneratorFamily_image_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ q : (↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G (verticesOf emb data)) ⧸
          LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                  kirchhoffSubmodule G (verticesOf emb data)))),
          q = 0 ↔
            AnnihilatesKempeClosureGeneratorFamily emb.faceBoundary C₀
              ((boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
                  emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) q :
                  theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data)) :
                  G.edgeSet → Color) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun q =>
    boundaryZeroProjectionKempeKirchhoffQuotientClass_eq_zero_iff_annihilatesKempeClosureGeneratorFamily_image_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := verticesOf emb data) (hboundary emb data) q⟩

/-- Graph-level orthogonality-facing criterion for the corrected `W₀(H)` quotient route. -/
theorem exists_boundaryZeroProjectionKempeKirchhoffQuotientClass_eq_zero_iff_image_mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ q : (↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G (verticesOf emb data)) ⧸
          LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                  kirchhoffSubmodule G (verticesOf emb data)))),
          q = 0 ↔
            ((boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
                emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) q :
                theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data)) :
                G.edgeSet → Color) ∈
              (chainDotBilinForm G.edgeSet).orthogonal
                (projectedKempeClosureGeneratorSubspace emb C₀) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun q =>
    boundaryZeroProjectionKempeKirchhoffQuotientClass_eq_zero_iff_image_mem_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := verticesOf emb data) (hboundary emb data) q⟩

/-- Graph-level `W₀(H) ∩ projectedSpanᗮ = 0` consequence of the corrected quotient route. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) ⊓
            (chainDotBilinForm G.edgeSet).orthogonal
              (projectedKempeClosureGeneratorSubspace emb C₀) =
          ⊥ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49BoundaryZeroKirchhoffSubspace_inf_chainDot_orthogonal_projectedKempeClosureGeneratorSubspace_eq_bot_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := verticesOf emb data) (hboundary emb data)⟩

/-- Graph-level detector form for nonzero corrected source quotient classes. -/
theorem exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_boundaryZeroProjectionKempeKirchhoffQuotientClass_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ q : (↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G (verticesOf emb data)) ⧸
          LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                  kirchhoffSubmodule G (verticesOf emb data)))),
          q ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
              chainDotBilinForm G.edgeSet p
                ((boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
                    emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) q :
                    theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data)) :
                    G.edgeSet → Color) ≠ 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun q hq =>
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_boundaryZeroProjectionKempeKirchhoffQuotientClass_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := verticesOf emb data) (hboundary emb data) hq⟩

/-- Graph-level detector form for nonzero concrete `W₀(H)` chains. -/
theorem exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          z ≠ 0 →
            ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun z hz =>
    exists_projectedKempeClosureGeneratorSubspace_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := verticesOf emb data) (hboundary emb data) hz⟩

/-- Graph-level pointwise `W₀(H)` orthogonality characterization against the projected
Definition 4.8 generator span. -/
theorem exists_theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
            z = 0 := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun z =>
    theorem49BoundaryZeroKirchhoffSubspace_chainDot_projectedKempeClosureGeneratorSubspace_eq_zero_iff_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := verticesOf emb data) (hboundary emb data)⟩

/-- Graph-level kernel form of the concrete `W₀(H)` pairing separation theorem. -/
theorem exists_ker_theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap_eq_bot_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        LinearMap.ker
            (theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
              (G := G) emb C₀ (verticesOf emb data)) =
          ⊥ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    ker_theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap_eq_bot_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := verticesOf emb data) (hboundary emb data)⟩

/-- Graph-level finite-dimensional consequence of the concrete `W₀(H)` pairing injection. -/
theorem exists_finrank_theorem49BoundaryZeroKirchhoffSubspace_le_finrank_projectedKempeClosureGeneratorSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        Module.finrank F2 (theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data)) ≤
          Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀) := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    finrank_theorem49BoundaryZeroKirchhoffSubspace_le_finrank_projectedKempeClosureGeneratorSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) (emb := emb) (data := data) (C₀ := C₀) (hC₀ := hC₀)
      (vertices := verticesOf emb data) (hboundary emb data)⟩

/-- Graph-level quotient-representative form of the corrected target bridge. -/
theorem exists_boundaryZeroProjectionKempeKirchhoffQuotientRepresentative_eq_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          ∃ x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G (verticesOf emb data)),
            boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
              emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data)
                (Submodule.Quotient.mk x) = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun z =>
    exists_boundaryZeroProjectionKempeKirchhoffQuotientRepresentative_eq_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) z⟩

/-- Graph-level inverse-equivalence representative form of the corrected target bridge. -/
theorem exists_boundaryZeroProjectionKempeKirchhoffQuotientRepresentative_symm_eq_mk_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data),
          ∃ x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G (verticesOf emb data)),
            (boundaryZeroProjectionKempeKirchhoffQuotientEquivBoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
                emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data)).symm z =
              Submodule.Quotient.mk x := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data, fun z =>
    exists_boundaryZeroProjectionKempeKirchhoffQuotientRepresentative_symm_eq_mk_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) z⟩

/-- Graph-level operational preimage form of the target quotient bridge. -/
theorem exists_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (verticesOf : ∀ emb : PlaneEmbeddingWithBoundary G,
      PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb → Finset V)
    (hboundary : ∀ emb : PlaneEmbeddingWithBoundary G,
      ∀ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ v ∈ verticesOf emb data,
          ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, v ∉ (e : Sym2 V)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb,
        ∀ {z : G.edgeSet → Color},
          z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (verticesOf emb data) →
            ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                kirchhoffSubmodule G (verticesOf emb data),
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  refine ⟨emb, data, ?_⟩
  intro z hz
  exact
    exists_kempeClosureGeneratorSubspace_inf_kirchhoffSubmodule_preimage_boundaryZeroProjection_of_mem_theorem49BoundaryZeroKirchhoffSubspace_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀ (verticesOf emb data) (hboundary emb data) hz

end Mettapedia.GraphTheory.FourColor
