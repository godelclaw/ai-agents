import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVertices
import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVerticesAnnulusConstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusGeometry
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusConstructionSpanning
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusRootInteriorDual

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- A route-level synthesis of the currently proved Theorem 4.9 endpoint over the selected-
boundary-purified interior-edge endpoint carrier. The carrier is the already-established
`selectedBoundaryInteriorEdgeEndpointVertices`; this package deliberately adds no new carrier
construction.

The fields collect the algebraic consequences needed downstream: boundary-erased image, pointwise
separation, projected-generator spanning, kernel-zero and finite-dimensional forms, and the
corrected raw-source quotient/decomposition. -/
structure Theorem49BoundaryRootSynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (C₀ : G.EdgeColoring Color) : Prop where
  target_eq_boundaryProjectionImage :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) =
      Submodule.map
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
        (kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
  pointwise_separation :
    ∀ z : theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb),
      (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
        z = 0
  pairing_ker_eq_bot :
    LinearMap.ker
        (theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
          (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb)) =
      ⊥
  finrank_le_projectedGeneratorSubspace :
    Module.finrank F2
        (theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb)) ≤
      Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀)
  target_eq_projectedGeneratorSource :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) =
      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
        projectedKempeClosureGeneratorSubspace emb C₀
  target_le_projectedGeneratorSubspace :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) ≤
      projectedKempeClosureGeneratorSubspace emb C₀
  target_le_projectedGeneratorFamilySpan :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) ≤
      Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀)
  target_eq_rawSourceImage :
    theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) =
      Submodule.map
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
        (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
  projectedGeneratorRepresentation :
    ∀ {z : G.edgeSet → Color},
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb) →
        ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
          (terms : Set (G.edgeSet → Color)) ⊆
              projectedKempeClosureGeneratorFamily emb C₀ ∧
            coeff.support ⊆ terms ∧
              ∑ y ∈ terms, coeff y • y = z
  rawGeneratorProjectionRepresentation :
    ∀ {z : G.edgeSet → Color},
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb) →
        ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
          (terms : Set (G.edgeSet → Color)) ⊆
              kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
            coeff.support ⊆ terms ∧
              (∑ y ∈ terms, coeff y • y) ∈
                  kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                    (∑ y ∈ terms, coeff y • y) = z
  rawSourcePreimage :
    ∀ {z : G.edgeSet → Color},
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb) →
        ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb),
          boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z
  rawKirchhoffRepresentative :
    ∀ {x : G.edgeSet → Color},
      x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) →
        ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
          (terms : Set (G.edgeSet → Color)) ⊆
              kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
            coeff.support ⊆ terms ∧
              (∑ y ∈ terms, coeff y • y) ∈
                  kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                    (∑ y ∈ terms, coeff y • y) =
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x
  rawBoundaryKernelDecomposition :
    ∀ {x : G.edgeSet → Color},
      x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) →
        ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
            (boundaryError : G.edgeSet → Color),
          (terms : Set (G.edgeSet → Color)) ⊆
              kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
            coeff.support ⊆ terms ∧
              (∑ y ∈ terms, coeff y • y) ∈
                  kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                boundaryError ∈
                    kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
                      LinearMap.ker
                        (boundaryZeroProjection
                          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
                  (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                    boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                        (∑ y ∈ terms, coeff y • y) =
                      boundaryZeroProjection
                        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x

/-- At any completed theorem-4.9 synthesis surface, the whole purified Kirchhoff submodule
splits as raw Definition 4.8 Kempe-source chains plus selected-boundary-kernel errors.  This is
the submodule-level form of the finite raw quotient/error decomposition field: every Kirchhoff
chain is the sum of a Kirchhoff-valid raw generator-family combination and an error killed by the
selected-boundary projection, and both summands stay inside the purified Kirchhoff submodule. -/
theorem Theorem49BoundaryRootSynthesis.kirchhoffSubmodule_eq_rawSource_sup_boundaryKernel
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) =
      (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) ⊔
        (kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
          LinearMap.ker
            (boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) := by
  apply le_antisymm
  · intro x hx
    rcases h.rawBoundaryKernelDecomposition hx with
      ⟨coeff, terms, boundaryError, hterms, hsupport, hkirch, herror, hsum, _hproj⟩
    let raw : G.edgeSet → Color := ∑ y ∈ terms, coeff y • y
    have hrawSpan :
        raw ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ := by
      have hrawSpan' :
          raw ∈ Submodule.span F2 (kempeClosureGeneratorFamily emb.faceBoundary C₀) :=
        (Submodule.mem_span_iff_exists_finset_subset
          (R := F2) (s := kempeClosureGeneratorFamily emb.faceBoundary C₀) (x := raw)).2
          ⟨coeff, terms, hterms, hsupport, rfl⟩
      simpa [kempeClosureGeneratorSubspace, raw] using hrawSpan'
    have hrawLeft :
        raw ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) := by
      exact ⟨hrawSpan, by simpa [raw] using hkirch⟩
    exact
      (Submodule.mem_sup).2
        ⟨raw, hrawLeft, boundaryError, herror, by simpa [raw] using hsum⟩
  · exact sup_le inf_le_right inf_le_left

/-- Quotient form of the raw-source/error decomposition.  Inside the purified Kirchhoff
submodule, quotienting by the selected-boundary kernel error makes the Kirchhoff-valid raw
Definition 4.8 source span all quotient classes. -/
theorem Theorem49BoundaryRootSynthesis.rawSource_mkQ_eq_top
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Submodule.map
        (Submodule.mkQ
          (LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)))))
        (Submodule.comap
          (kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb)).subtype
          (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb))) =
      ⊤ := by
  let boundary : Finset G.edgeSet :=
    selectedBoundarySupport emb.faceBoundary emb.faces emb.faces
  let K : Submodule F2 (G.edgeSet → Color) :=
    kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)
  let R : Submodule F2 (G.edgeSet → Color) :=
    kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ K
  let BQ : Submodule F2 K :=
    LinearMap.ker ((boundaryZeroProjection boundary).domRestrict K)
  let RQ : Submodule F2 K := Submodule.comap K.subtype R
  change Submodule.map (Submodule.mkQ BQ) RQ = ⊤
  rw [Submodule.map_mkQ_eq_top]
  apply le_antisymm
  · exact le_top
  · intro x _hx
    have hxSup :
        (x : G.edgeSet → Color) ∈
          R ⊔ (K ⊓ LinearMap.ker (boundaryZeroProjection boundary)) := by
      have hxK :
          (x : G.edgeSet → Color) ∈
            kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) := by
        change (x : G.edgeSet → Color) ∈ K
        exact x.property
      change
        (x : G.edgeSet → Color) ∈
          (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) ⊔
            (kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
              LinearMap.ker
                (boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
      rw [← h.kirchhoffSubmodule_eq_rawSource_sup_boundaryKernel]
      exact hxK
    rcases (Submodule.mem_sup).1 hxSup with ⟨raw, hraw, boundaryError, herror, hsum⟩
    have hrawK : raw ∈ K := hraw.2
    have herrorK : boundaryError ∈ K := herror.1
    have herrorBQ : (⟨boundaryError, herrorK⟩ : K) ∈ BQ := by
      change boundaryZeroProjection boundary boundaryError = 0
      exact herror.2
    have hrawRQ : (⟨raw, hrawK⟩ : K) ∈ RQ := by
      change raw ∈ R
      exact hraw
    exact
      (Submodule.mem_sup).2
        ⟨⟨boundaryError, herrorK⟩, herrorBQ, ⟨raw, hrawK⟩, hrawRQ,
          Subtype.ext (by simpa [add_comm] using hsum)⟩

/-- Dimension consequence of the raw quotient surjectivity: the selected-boundary quotient of the
purified Kirchhoff submodule has dimension bounded by the Kirchhoff-valid raw Definition 4.8
source submodule inside it. -/
theorem Theorem49BoundaryRootSynthesis.finrank_quotient_le_rawSource
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Module.finrank F2
        (kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
          LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)))) ≤
      Module.finrank F2
        (Submodule.comap
          (kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb)).subtype
          (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb))) := by
  let boundary : Finset G.edgeSet :=
    selectedBoundarySupport emb.faceBoundary emb.faces emb.faces
  let K : Submodule F2 (G.edgeSet → Color) :=
    kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)
  let BQ : Submodule F2 K :=
    LinearMap.ker ((boundaryZeroProjection boundary).domRestrict K)
  let RQ : Submodule F2 K :=
    Submodule.comap K.subtype (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓ K)
  change Module.finrank F2 (K ⧸ BQ) ≤ Module.finrank F2 RQ
  have htop : Submodule.map (Submodule.mkQ BQ) RQ = ⊤ := by
    simpa [boundary, K, BQ, RQ] using h.rawSource_mkQ_eq_top
  calc
    Module.finrank F2 (K ⧸ BQ)
        = Module.finrank F2 (⊤ : Submodule F2 (K ⧸ BQ)) := by
          rw [finrank_top]
    _ = Module.finrank F2 (Submodule.map (Submodule.mkQ BQ) RQ) := by
          rw [htop]
    _ ≤ Module.finrank F2 RQ := Submodule.finrank_map_le (Submodule.mkQ BQ) RQ

/-- Target-dimension consequence of the corrected raw-source image: the concrete boundary-zero
Kirchhoff target has dimension bounded by the Kirchhoff-valid raw Definition 4.8 source submodule
that maps onto it. -/
theorem Theorem49BoundaryRootSynthesis.finrank_target_le_rawSource
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Module.finrank F2
        (theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb)) ≤
      Module.finrank F2
        ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) := by
  rw [h.target_eq_rawSourceImage]
  exact
    Submodule.finrank_map_le
      (boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
      (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
        kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))

/-- First-isomorphism form carried by the synthesis surface itself: the purified Kirchhoff
submodule modulo the selected-boundary projection kernel is linearly equivalent to the concrete
boundary-zero Kirchhoff target. -/
noncomputable def Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    (kirchhoffSubmodule G
        (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            (kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb)))) ≃ₗ[F2]
      theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) :=
  (boundaryZeroProjectionKirchhoffQuotientEquivImage
      (G := G)
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
      (selectedBoundaryInteriorEdgeEndpointVertices emb)).trans
    (LinearEquiv.ofEq _ _ h.target_eq_boundaryProjectionImage.symm)

/-- The synthesis-surface quotient equivalence sends the quotient class of a purified Kirchhoff
chain to its selected-boundary-erased chain in the concrete theorem-4.9 target. -/
theorem Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget_apply_mk
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ((h.boundaryProjectionQuotientEquivTarget (Submodule.Quotient.mk x) :
        theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
        G.edgeSet → Color) =
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
        (x : G.edgeSet → Color) := by
  rw [Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget]
  simp [boundaryZeroProjectionKirchhoffQuotientEquivImage_apply_mk]

/-- The projected-generator pairing map transported from the concrete theorem-4.9 target to the
purified Kirchhoff quotient.  It pairs a quotient class with projected Definition 4.8 generators
after selected-boundary erasure. -/
noncomputable def Theorem49BoundaryRootSynthesis.kirchhoffQuotientProjectedGeneratorPairingMap
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    (kirchhoffSubmodule G
        (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            (kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb)))) →ₗ[F2]
      (projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2) :=
  (theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
    (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb)).comp
      h.boundaryProjectionQuotientEquivTarget.toLinearMap

/-- On a quotient class represented by a purified Kirchhoff chain, the quotient pairing map is
computed by selected-boundary erasure followed by the chain-dot pairing with a projected
Definition 4.8 generator. -/
theorem Theorem49BoundaryRootSynthesis.kirchhoffQuotientProjectedGeneratorPairingMap_apply_mk
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (p : projectedKempeClosureGeneratorSubspace emb C₀) :
    h.kirchhoffQuotientProjectedGeneratorPairingMap (Submodule.Quotient.mk x) p =
      chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
          (x : G.edgeSet → Color)) := by
  rw [Theorem49BoundaryRootSynthesis.kirchhoffQuotientProjectedGeneratorPairingMap]
  change
    chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)
        ((h.boundaryProjectionQuotientEquivTarget (Submodule.Quotient.mk x) :
          theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
          G.edgeSet → Color) =
      chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
          (x : G.edgeSet → Color))
  rw [Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget_apply_mk]

/-- The quotient-level projected-generator pairing has trivial kernel at any completed
theorem-4.9 synthesis surface. -/
theorem Theorem49BoundaryRootSynthesis.ker_kirchhoffQuotientProjectedGeneratorPairingMap_eq_bot
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    LinearMap.ker h.kirchhoffQuotientProjectedGeneratorPairingMap = ⊥ := by
  apply le_antisymm
  · intro q hq
    have hz_mem :
        h.boundaryProjectionQuotientEquivTarget q ∈
          LinearMap.ker
            (theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
              (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb)) := by
      change
        theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
            (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb)
            (h.boundaryProjectionQuotientEquivTarget q) = 0
      simpa [Theorem49BoundaryRootSynthesis.kirchhoffQuotientProjectedGeneratorPairingMap]
        using hq
    have hz_zero : h.boundaryProjectionQuotientEquivTarget q = 0 := by
      have hz_bot :
          h.boundaryProjectionQuotientEquivTarget q ∈
            (⊥ : Submodule F2
              (theorem49BoundaryZeroKirchhoffSubspace emb
                (selectedBoundaryInteriorEdgeEndpointVertices emb))) := by
        simpa [h.pairing_ker_eq_bot] using hz_mem
      simpa using hz_bot
    have hq_zero : q = 0 :=
      h.boundaryProjectionQuotientEquivTarget.injective (by simpa using hz_zero)
    simpa using hq_zero
  · exact bot_le

/-- Quotient-level nondegeneracy in linear-map form: the projected-generator pairing map
vanishes on a purified Kirchhoff quotient class exactly when that quotient class is zero. -/
theorem Theorem49BoundaryRootSynthesis.kirchhoffQuotientProjectedGeneratorPairingMap_eq_zero_iff
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (q :
      kirchhoffSubmodule G
          (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
        LinearMap.ker
          ((boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
              (kirchhoffSubmodule G
                (selectedBoundaryInteriorEdgeEndpointVertices emb)))) :
    h.kirchhoffQuotientProjectedGeneratorPairingMap q = 0 ↔ q = 0 := by
  constructor
  · intro hq
    have hqKer : q ∈ LinearMap.ker h.kirchhoffQuotientProjectedGeneratorPairingMap := hq
    have hqBot :
        q ∈ (⊥ : Submodule F2
          (kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
            LinearMap.ker
              ((boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                  (kirchhoffSubmodule G
                    (selectedBoundaryInteriorEdgeEndpointVertices emb))))) := by
      simpa [h.ker_kirchhoffQuotientProjectedGeneratorPairingMap_eq_bot] using hqKer
    simpa using hqBot
  · intro hq
    simp [hq]

/-- Any nonzero purified Kirchhoff quotient class is detected by evaluating the quotient-level
pairing map at some projected Definition 4.8 generator. -/
theorem Theorem49BoundaryRootSynthesis.exists_projectedGenerator_pairingMap_ne_zero_of_ne_zero_kirchhoffQuotientClass
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (q :
      kirchhoffSubmodule G
          (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
        LinearMap.ker
          ((boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
              (kirchhoffSubmodule G
                (selectedBoundaryInteriorEdgeEndpointVertices emb))))
    (hq : q ≠ 0) :
    ∃ p : projectedKempeClosureGeneratorSubspace emb C₀,
      h.kirchhoffQuotientProjectedGeneratorPairingMap q p ≠ 0 := by
  have hmap_ne : h.kirchhoffQuotientProjectedGeneratorPairingMap q ≠ 0 := by
    intro hzero
    exact hq ((h.kirchhoffQuotientProjectedGeneratorPairingMap_eq_zero_iff q).1 hzero)
  by_contra hnone
  apply hmap_ne
  ext p
  by_contra hp
  exact hnone ⟨p, hp⟩

/-- Dimension consequence of the quotient-level projected-generator pairing: once the pairing
map on the purified Kirchhoff quotient has trivial kernel, the quotient dimension is bounded by
the projected Definition 4.8 generator subspace itself. -/
theorem Theorem49BoundaryRootSynthesis.finrank_kirchhoffQuotient_le_projectedGeneratorSubspace
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Module.finrank F2
        (kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
          LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)))) ≤
      Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀) := by
  let L := h.kirchhoffQuotientProjectedGeneratorPairingMap
  have hker : LinearMap.ker L = ⊥ := by
    simpa [L] using h.ker_kirchhoffQuotientProjectedGeneratorPairingMap_eq_bot
  have hinj : Function.Injective L := (LinearMap.ker_eq_bot).1 hker
  have hleDual :
      Module.finrank F2
          (kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
            LinearMap.ker
              ((boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                  (kirchhoffSubmodule G
                    (selectedBoundaryInteriorEdgeEndpointVertices emb)))) ≤
        Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2) :=
    LinearMap.finrank_le_finrank_of_injective (f := L) hinj
  simpa [L, Module.Dual] using
    hleDual.trans_eq
      (Subspace.dual_finrank_eq
        (K := F2) (V := projectedKempeClosureGeneratorSubspace emb C₀))

/-- The image of the quotient-level projected-generator pairing map has exactly the dimension
of the purified Kirchhoff quotient.  This identifies the quotient with a concrete subspace of
the dual of the projected Definition 4.8 generator subspace. -/
theorem Theorem49BoundaryRootSynthesis.finrank_range_kirchhoffQuotientProjectedGeneratorPairingMap
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Module.finrank F2 (LinearMap.range h.kirchhoffQuotientProjectedGeneratorPairingMap) =
      Module.finrank F2
        (kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
          LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)))) := by
  let L := h.kirchhoffQuotientProjectedGeneratorPairingMap
  have hker : LinearMap.ker L = ⊥ := by
    simpa [L] using h.ker_kirchhoffQuotientProjectedGeneratorPairingMap_eq_bot
  have hinj : Function.Injective L := (LinearMap.ker_eq_bot).1 hker
  simpa [L] using (LinearMap.finrank_range_of_inj (f := L) hinj)

/-- The purified Kirchhoff quotient is linearly equivalent to the image of its quotient-level
projected-generator pairing map.  This makes the pairing-map image the concrete dual-subspace
model of the quotient/error surface. -/
noncomputable def Theorem49BoundaryRootSynthesis.kirchhoffQuotientEquivPairingMapRange
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    (kirchhoffSubmodule G
        (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            (kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb)))) ≃ₗ[F2]
      LinearMap.range h.kirchhoffQuotientProjectedGeneratorPairingMap := by
  let L := h.kirchhoffQuotientProjectedGeneratorPairingMap
  have hker : LinearMap.ker L = ⊥ := by
    simpa [L] using h.ker_kirchhoffQuotientProjectedGeneratorPairingMap_eq_bot
  exact LinearEquiv.ofInjective L ((LinearMap.ker_eq_bot).1 hker)

/-- The range equivalence sends a purified quotient class to the corresponding
projected-generator functional in the pairing-map image. -/
theorem Theorem49BoundaryRootSynthesis.kirchhoffQuotientEquivPairingMapRange_apply
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (q :
      kirchhoffSubmodule G
          (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
        LinearMap.ker
          ((boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
              (kirchhoffSubmodule G
                (selectedBoundaryInteriorEdgeEndpointVertices emb)))) :
    (h.kirchhoffQuotientEquivPairingMapRange q :
        projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2) =
      h.kirchhoffQuotientProjectedGeneratorPairingMap q := by
  rw [Theorem49BoundaryRootSynthesis.kirchhoffQuotientEquivPairingMapRange]
  rfl

/-- On quotient classes represented by purified Kirchhoff chains, the range equivalence is still
computed by selected-boundary erasure followed by the chain-dot pairing with projected
Definition 4.8 generators. -/
theorem Theorem49BoundaryRootSynthesis.kirchhoffQuotientEquivPairingMapRange_apply_mk
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (p : projectedKempeClosureGeneratorSubspace emb C₀) :
    (h.kirchhoffQuotientEquivPairingMapRange (Submodule.Quotient.mk x) :
        projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2) p =
      chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
          (x : G.edgeSet → Color)) := by
  rw [Theorem49BoundaryRootSynthesis.kirchhoffQuotientEquivPairingMapRange_apply]
  exact h.kirchhoffQuotientProjectedGeneratorPairingMap_apply_mk x p

/-- Raw-source first-isomorphism form carried by the synthesis surface: the Kirchhoff-valid raw
Definition 4.8 source submodule modulo the selected-boundary projection kernel is linearly
equivalent to the concrete boundary-zero Kirchhoff target. -/
noncomputable def Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivTarget
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    (((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
        kirchhoffSubmodule G
          (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
          Submodule F2 (G.edgeSet → Color)) ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G
                (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
              Submodule F2 (G.edgeSet → Color)))) ≃ₗ[F2]
      theorem49BoundaryZeroKirchhoffSubspace emb
        (selectedBoundaryInteriorEdgeEndpointVertices emb) :=
  (boundaryZeroProjectionSubmoduleQuotientEquivImage
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
      (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
        kirchhoffSubmodule G
          (selectedBoundaryInteriorEdgeEndpointVertices emb))).trans
    (LinearEquiv.ofEq _ _ h.target_eq_rawSourceImage.symm)

/-- The raw-source quotient equivalence sends the class of a Kirchhoff-valid raw source chain to
its selected-boundary-erased chain in the concrete theorem-4.9 target. -/
theorem Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivTarget_apply_mk
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))) :
    ((h.rawSourceQuotientEquivTarget (Submodule.Quotient.mk x) :
        theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
        G.edgeSet → Color) =
      boundaryZeroProjection
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
        (x : G.edgeSet → Color) := by
  rw [Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivTarget]
  simp [boundaryZeroProjectionSubmoduleQuotientEquivImage_apply_mk]

/-- The raw-source quotient and the purified Kirchhoff quotient are linearly equivalent at any
completed synthesis surface.  This is the inclusion of the raw Definition 4.8 source modulo
selected-boundary error, expressed through the common concrete theorem-4.9 target. -/
noncomputable def Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    (((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
        kirchhoffSubmodule G
          (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
          Submodule F2 (G.edgeSet → Color)) ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G
                (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
              Submodule F2 (G.edgeSet → Color)))) ≃ₗ[F2]
      (kirchhoffSubmodule G
        (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            (kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb)))) :=
  h.rawSourceQuotientEquivTarget.trans h.boundaryProjectionQuotientEquivTarget.symm

/-- Under the quotient bridge from the raw source quotient to the purified Kirchhoff quotient, a
raw Kirchhoff-valid source representative is sent to the same chain regarded as a purified
Kirchhoff quotient representative. -/
theorem Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient_apply_mk
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))) :
    h.rawSourceQuotientEquivKirchhoffQuotient (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨(x : G.edgeSet → Color), x.property.2⟩ :
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) := by
  apply h.boundaryProjectionQuotientEquivTarget.injective
  apply Subtype.ext
  simp [Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient,
    Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivTarget_apply_mk,
    Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget_apply_mk]

/-- The raw Definition 4.8 source quotient has the same concrete pairing-map image model as the
purified Kirchhoff quotient.  This is the direct quotient/error-to-dual-subspace bridge: a raw
Kirchhoff-valid source class modulo selected-boundary error is represented as a functional in the
image of the quotient-level projected-generator pairing map. -/
noncomputable def Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivPairingMapRange
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    (((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
        kirchhoffSubmodule G
          (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
          Submodule F2 (G.edgeSet → Color)) ⧸
      LinearMap.ker
        ((boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
            ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G
                (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
              Submodule F2 (G.edgeSet → Color)))) ≃ₗ[F2]
      LinearMap.range h.kirchhoffQuotientProjectedGeneratorPairingMap :=
  h.rawSourceQuotientEquivKirchhoffQuotient.trans h.kirchhoffQuotientEquivPairingMapRange

/-- On raw-source quotient classes, the direct image model is computed by selected-boundary
erasure followed by the chain-dot pairing with projected Definition 4.8 generators. -/
theorem Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivPairingMapRange_apply_mk
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)))
    (p : projectedKempeClosureGeneratorSubspace emb C₀) :
    (h.rawSourceQuotientEquivPairingMapRange (Submodule.Quotient.mk x) :
        projectedKempeClosureGeneratorSubspace emb C₀ →ₗ[F2] F2) p =
      chainDotBilinForm G.edgeSet (p : G.edgeSet → Color)
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
          (x : G.edgeSet → Color)) := by
  simpa [Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivPairingMapRange,
    Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient_apply_mk]
    using
      (h.kirchhoffQuotientEquivPairingMapRange_apply_mk
        (⟨(x : G.edgeSet → Color), x.property.2⟩ :
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) p)

/-- The raw Definition 4.8 source quotient has exactly the dimension of the concrete
pairing-map image.  This is the finite-dimensional shadow of the direct raw-source
quotient/error-to-dual-subspace model. -/
theorem Theorem49BoundaryRootSynthesis.finrank_rawSourceQuotient_eq_pairingMapRange
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Module.finrank F2
        (((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
            Submodule F2 (G.edgeSet → Color)) ⧸
        LinearMap.ker
          ((boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
              ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
                Submodule F2 (G.edgeSet → Color)))) =
      Module.finrank F2 (LinearMap.range h.kirchhoffQuotientProjectedGeneratorPairingMap) := by
  simpa using h.rawSourceQuotientEquivPairingMapRange.finrank_eq

/-- The raw Definition 4.8 source quotient is bounded by the projected Definition 4.8 generator
subspace.  Unlike the earlier ambient raw-source bound, this consequence factors through the
pairing-map image and the purified quotient's nondegenerate projected-generator pairing. -/
theorem Theorem49BoundaryRootSynthesis.finrank_rawSourceQuotient_le_projectedGeneratorSubspace
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀) :
    Module.finrank F2
        (((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
            Submodule F2 (G.edgeSet → Color)) ⧸
        LinearMap.ker
          ((boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
              ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
                Submodule F2 (G.edgeSet → Color)))) ≤
      Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀) := by
  calc
    Module.finrank F2
        (((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
            Submodule F2 (G.edgeSet → Color)) ⧸
        LinearMap.ker
          ((boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
              ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
                Submodule F2 (G.edgeSet → Color))))
        = Module.finrank F2
            (LinearMap.range h.kirchhoffQuotientProjectedGeneratorPairingMap) :=
          h.finrank_rawSourceQuotient_eq_pairingMapRange
    _ = Module.finrank F2
          (kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
            LinearMap.ker
              ((boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                  (kirchhoffSubmodule G
                    (selectedBoundaryInteriorEdgeEndpointVertices emb)))) :=
          h.finrank_range_kirchhoffQuotientProjectedGeneratorPairingMap
    _ ≤ Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀) :=
          h.finrank_kirchhoffQuotient_le_projectedGeneratorSubspace

/-- Every purified Kirchhoff quotient class has a finite raw Definition 4.8 generator-sum
representative.  The representative is a Kirchhoff-valid raw source chain, and it represents the
same class modulo the selected-boundary projection kernel as the original purified Kirchhoff
chain. -/
theorem Theorem49BoundaryRootSynthesis.exists_rawGeneratorSum_for_kirchhoffQuotientClass
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    ∃ (raw : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)))
        (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
      (terms : Set (G.edgeSet → Color)) ⊆
          kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) = (raw : G.edgeSet → Color) ∧
            (Submodule.Quotient.mk
                (⟨(raw : G.edgeSet → Color), raw.property.2⟩ :
                  kirchhoffSubmodule G
                    (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
              kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
                LinearMap.ker
                  ((boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                      (kirchhoffSubmodule G
                        (selectedBoundaryInteriorEdgeEndpointVertices emb)))) =
              Submodule.Quotient.mk x := by
  rcases h.rawKirchhoffRepresentative x.property with
    ⟨coeff, terms, hterms, hsupport, hrawKirch, hproj⟩
  let rawChain : G.edgeSet → Color := ∑ y ∈ terms, coeff y • y
  have hrawSpan :
      rawChain ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ := by
    have hrawSpan' :
        rawChain ∈ Submodule.span F2 (kempeClosureGeneratorFamily emb.faceBoundary C₀) :=
      (Submodule.mem_span_iff_exists_finset_subset
        (R := F2) (s := kempeClosureGeneratorFamily emb.faceBoundary C₀)
        (x := rawChain)).2
        ⟨coeff, terms, hterms, hsupport, rfl⟩
    simpa [kempeClosureGeneratorSubspace, rawChain] using hrawSpan'
  let raw : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :=
    ⟨rawChain, hrawSpan, by simpa [rawChain] using hrawKirch⟩
  refine ⟨raw, coeff, terms, hterms, hsupport, by simp [raw, rawChain], ?_⟩
  exact
    (boundaryZeroProjectionSubmoduleQuotient_mk_eq_mk_iff
      (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
      (S := kirchhoffSubmodule G
        (selectedBoundaryInteriorEdgeEndpointVertices emb))).2
      (by simpa [raw, rawChain] using hproj)

/-- Quotient-class form of the theorem-4.9 separation endpoint: a purified Kirchhoff quotient
class is zero exactly when its selected-boundary-erased representative pairs to zero with every
projected Definition 4.8 generator. -/
theorem Theorem49BoundaryRootSynthesis.kirchhoffQuotientClass_eq_zero_iff_projectedGenerator_orthogonal
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
    (Submodule.Quotient.mk x :
        kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
          LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)))) = 0 ↔
      ∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
            (x : G.edgeSet → Color)) = 0 := by
  let q :
      kirchhoffSubmodule G
          (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
        LinearMap.ker
          ((boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
              (kirchhoffSubmodule G
                (selectedBoundaryInteriorEdgeEndpointVertices emb))) :=
    Submodule.Quotient.mk x
  let z : theorem49BoundaryZeroKirchhoffSubspace emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb) :=
    h.boundaryProjectionQuotientEquivTarget q
  constructor
  · intro hq p hp
    have hz : z = 0 := by
      simp [z, q, hq]
    have horth := (h.pointwise_separation z).2 hz
    simpa [z, q,
      Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget_apply_mk]
      using horth p hp
  · intro horth
    have horthTarget :
        ∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0 := by
      intro p hp
      simpa [z, q,
        Theorem49BoundaryRootSynthesis.boundaryProjectionQuotientEquivTarget_apply_mk]
        using horth p hp
    have hz : z = 0 := (h.pointwise_separation z).1 horthTarget
    apply h.boundaryProjectionQuotientEquivTarget.injective
    simpa [z, q] using hz

/-- Nonzero purified Kirchhoff quotient classes are detected by a projected Definition 4.8
generator after selected-boundary erasure. -/
theorem Theorem49BoundaryRootSynthesis.exists_projectedGenerator_chainDot_ne_zero_of_ne_zero_kirchhoffQuotientClass
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (hx :
      (Submodule.Quotient.mk x :
          kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
            LinearMap.ker
              ((boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                  (kirchhoffSubmodule G
                    (selectedBoundaryInteriorEdgeEndpointVertices emb)))) ≠ 0) :
    ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
          (x : G.edgeSet → Color)) ≠ 0 := by
  by_contra hnone
  have horth :
      ∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
            (x : G.edgeSet → Color)) = 0 := by
    intro p hp
    by_contra hne
    exact hnone ⟨p, hp, hne⟩
  exact hx
    ((h.kirchhoffQuotientClass_eq_zero_iff_projectedGenerator_orthogonal x).2 horth)

/-- Raw-source quotient-class separation: a Kirchhoff-valid raw Definition 4.8 source class
modulo selected-boundary error is zero exactly when its selected-boundary-erased representative
pairs trivially with every projected Definition 4.8 generator. -/
theorem Theorem49BoundaryRootSynthesis.rawSourceQuotientClass_eq_zero_iff_projectedGenerator_orthogonal
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))) :
    (Submodule.Quotient.mk x :
        ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
            Submodule F2 (G.edgeSet → Color)) ⧸
        LinearMap.ker
          ((boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
              ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
                Submodule F2 (G.edgeSet → Color)))) = 0 ↔
      ∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
            (x : G.edgeSet → Color)) = 0 := by
  let xKirch :
      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) :=
    ⟨(x : G.edgeSet → Color), x.property.2⟩
  have hiff :=
    h.kirchhoffQuotientClass_eq_zero_iff_projectedGenerator_orthogonal xKirch
  constructor
  · intro hxZero
    have hxKirchZero :
        (Submodule.Quotient.mk xKirch :
          kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
            LinearMap.ker
              ((boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                  (kirchhoffSubmodule G
                    (selectedBoundaryInteriorEdgeEndpointVertices emb)))) = 0 := by
      have hmap :=
        congrArg h.rawSourceQuotientEquivKirchhoffQuotient hxZero
      simpa [xKirch,
        Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient_apply_mk]
        using hmap
    simpa [xKirch] using hiff.1 hxKirchZero
  · intro horth
    have hxKirchZero :
        (Submodule.Quotient.mk xKirch :
          kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
            LinearMap.ker
              ((boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                  (kirchhoffSubmodule G
                    (selectedBoundaryInteriorEdgeEndpointVertices emb)))) = 0 := by
      exact hiff.2 (by simpa [xKirch] using horth)
    apply h.rawSourceQuotientEquivKirchhoffQuotient.injective
    simpa [xKirch,
      Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient_apply_mk]
      using hxKirchZero

/-- Nonzero raw-source quotient classes are detected by some projected Definition 4.8 generator
after selected-boundary erasure. -/
theorem Theorem49BoundaryRootSynthesis.exists_projectedGenerator_chainDot_ne_zero_of_ne_zero_rawSourceQuotientClass
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)))
    (hx :
      (Submodule.Quotient.mk x :
        ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
            Submodule F2 (G.edgeSet → Color)) ⧸
        LinearMap.ker
          ((boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
              ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
                Submodule F2 (G.edgeSet → Color)))) ≠ 0) :
    ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
      chainDotBilinForm G.edgeSet p
        (boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
          (x : G.edgeSet → Color)) ≠ 0 := by
  by_contra hnone
  have horth :
      ∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
            (x : G.edgeSet → Color)) = 0 := by
    intro p hp
    by_contra hne
    exact hnone ⟨p, hp, hne⟩
  exact hx
    ((h.rawSourceQuotientClass_eq_zero_iff_projectedGenerator_orthogonal x).2 horth)

/-- A nonzero purified Kirchhoff quotient class has a finite raw generator-sum representative
that is itself detected by a projected Definition 4.8 generator.  This combines the
representative endpoint with quotient-level separation, so downstream arguments can work with a
raw finite source representative without losing the nonzero projected-pairing witness. -/
theorem Theorem49BoundaryRootSynthesis.exists_rawGeneratorSum_and_projectedGenerator_chainDot_ne_zero_of_ne_zero_kirchhoffQuotientClass
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (hx :
      (Submodule.Quotient.mk x :
          kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
            LinearMap.ker
              ((boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                  (kirchhoffSubmodule G
                    (selectedBoundaryInteriorEdgeEndpointVertices emb)))) ≠ 0) :
    ∃ (raw : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)))
        (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (p : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆
          kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) = (raw : G.edgeSet → Color) ∧
            (Submodule.Quotient.mk
                (⟨(raw : G.edgeSet → Color), raw.property.2⟩ :
                  kirchhoffSubmodule G
                    (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
              kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
                LinearMap.ker
                  ((boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                      (kirchhoffSubmodule G
                        (selectedBoundaryInteriorEdgeEndpointVertices emb)))) =
              Submodule.Quotient.mk x ∧
            p ∈ projectedKempeClosureGeneratorSubspace emb C₀ ∧
              chainDotBilinForm G.edgeSet p
                (boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                  (raw : G.edgeSet → Color)) ≠ 0 := by
  rcases h.exists_rawGeneratorSum_for_kirchhoffQuotientClass x with
    ⟨raw, coeff, terms, hterms, hsupport, hsum, hquot⟩
  have hrawQuotient_ne_zero :
      (Submodule.Quotient.mk
          (⟨(raw : G.edgeSet → Color), raw.property.2⟩ :
            kirchhoffSubmodule G
              (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
        kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
          LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)))) ≠ 0 := by
    intro hzero
    exact hx (by simpa [hquot] using hzero)
  rcases
    h.exists_projectedGenerator_chainDot_ne_zero_of_ne_zero_kirchhoffQuotientClass
      (⟨(raw : G.edgeSet → Color), raw.property.2⟩ :
        kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb))
      hrawQuotient_ne_zero with
    ⟨p, hp, hdetect⟩
  exact ⟨raw, coeff, terms, p, hterms, hsupport, hsum, hquot, hp, hdetect⟩

/-- A nonzero raw-source quotient class has a finite raw generator-sum representative that is
detected after selected-boundary erasure by a projected Definition 4.8 generator.  This is the
raw-source quotient version of the purified Kirchhoff representative theorem, with the quotient
bridge discharged inside the statement. -/
theorem Theorem49BoundaryRootSynthesis.exists_rawGeneratorSum_and_projectedGenerator_chainDot_ne_zero_of_ne_zero_rawSourceQuotientClass
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (x : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)))
    (hx :
      (Submodule.Quotient.mk x :
        ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
            Submodule F2 (G.edgeSet → Color)) ⧸
        LinearMap.ker
          ((boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
              ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
                Submodule F2 (G.edgeSet → Color)))) ≠ 0) :
    ∃ (raw : ↥(kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)))
        (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (p : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆
          kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) = (raw : G.edgeSet → Color) ∧
            (Submodule.Quotient.mk raw :
              ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
                  Submodule F2 (G.edgeSet → Color)) ⧸
              LinearMap.ker
                ((boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                    ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                      kirchhoffSubmodule G
                        (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
                      Submodule F2 (G.edgeSet → Color)))) =
              Submodule.Quotient.mk x ∧
            p ∈ projectedKempeClosureGeneratorSubspace emb C₀ ∧
              chainDotBilinForm G.edgeSet p
                (boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                  (raw : G.edgeSet → Color)) ≠ 0 := by
  let xKirch :
      kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) :=
    ⟨(x : G.edgeSet → Color), x.property.2⟩
  have hxKirch :
      (Submodule.Quotient.mk xKirch :
        kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb) ⧸
          LinearMap.ker
            ((boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
                (kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)))) ≠ 0 := by
    intro hxKirchZero
    apply hx
    apply h.rawSourceQuotientEquivKirchhoffQuotient.injective
    simpa [xKirch,
      Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient_apply_mk]
      using hxKirchZero
  rcases
    h.exists_rawGeneratorSum_and_projectedGenerator_chainDot_ne_zero_of_ne_zero_kirchhoffQuotientClass
      xKirch hxKirch with
    ⟨raw, coeff, terms, p, hterms, hsupport, hsum, hkirchQuot, hp, hdetect⟩
  have hrawQuot :
      (Submodule.Quotient.mk raw :
        ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
          kirchhoffSubmodule G
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
            Submodule F2 (G.edgeSet → Color)) ⧸
        LinearMap.ker
          ((boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)).domRestrict
              ((kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
                kirchhoffSubmodule G
                  (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
                Submodule F2 (G.edgeSet → Color)))) =
          Submodule.Quotient.mk x := by
    apply h.rawSourceQuotientEquivKirchhoffQuotient.injective
    simpa [xKirch,
      Theorem49BoundaryRootSynthesis.rawSourceQuotientEquivKirchhoffQuotient_apply_mk]
      using hkirchQuot
  exact ⟨raw, coeff, terms, p, hterms, hsupport, hsum, hrawQuot, hp, hdetect⟩

/-- A nonzero concrete theorem-4.9 target has a finite raw Definition 4.8 generator-sum
representative and is detected by a projected Definition 4.8 generator.  This combines the raw
projection representation field with pointwise projected-generator separation, so downstream
arguments can consume a nonzero boundary-zero Kirchhoff target without separately choosing a raw
representative and then proving a detector. -/
theorem Theorem49BoundaryRootSynthesis.exists_rawGeneratorSum_and_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (z : theorem49BoundaryZeroKirchhoffSubspace emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (hz : z ≠ 0) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (p : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆
          kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          (∑ y ∈ terms, coeff y • y) ∈
              kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
            boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                (∑ y ∈ terms, coeff y • y) =
              (z : G.edgeSet → Color) ∧
            p ∈ projectedKempeClosureGeneratorSubspace emb C₀ ∧
              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  rcases h.rawGeneratorProjectionRepresentation z.property with
    ⟨coeff, terms, hterms, hsupport, hkirch, hproj⟩
  have hdetector :
      ∃ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
        chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
    by_contra hnone
    have horth :
        ∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0 := by
      intro p hp
      by_contra hne
      exact hnone ⟨p, hp, hne⟩
    exact hz ((h.pointwise_separation z).1 horth)
  rcases hdetector with ⟨p, hp, hpair⟩
  exact ⟨coeff, terms, p, hterms, hsupport, hkirch, hproj, hp, hpair⟩

/-- A nonzero concrete theorem-4.9 target forces genuinely nonempty raw and projected
Definition 4.8 data.  The finite raw generator-family representative cannot be the empty sum,
because its selected-boundary erasure is the nonzero target, and the projected detector cannot be
the zero chain because its chain-dot pairing with that target is nonzero. -/
theorem Theorem49BoundaryRootSynthesis.exists_nonempty_rawGeneratorSum_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (z : theorem49BoundaryZeroKirchhoffSubspace emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (hz : z ≠ 0) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (p : G.edgeSet → Color),
      terms.Nonempty ∧
        (terms : Set (G.edgeSet → Color)) ⊆
            kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
          coeff.support ⊆ terms ∧
            (∑ y ∈ terms, coeff y • y) ∈
                kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
              boundaryZeroProjection
                (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                  (∑ y ∈ terms, coeff y • y) =
                (z : G.edgeSet → Color) ∧
              p ∈ projectedKempeClosureGeneratorSubspace emb C₀ ∧
                p ≠ 0 ∧
                  chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  rcases
    h.exists_rawGeneratorSum_and_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
      z hz with
    ⟨coeff, terms, p, hterms, hsupport, hkirch, hproj, hp, hpair⟩
  have htermsNonempty : terms.Nonempty := by
    by_contra hnot
    have htermsEmpty : terms = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    apply hz
    apply Subtype.ext
    simpa [htermsEmpty] using hproj.symm
  have hpNonzero : p ≠ 0 := by
    intro hpZero
    exact hpair (by simp [hpZero])
  exact
    ⟨coeff, terms, p, htermsNonempty, hterms, hsupport, hkirch, hproj, hp,
      hpNonzero, hpair⟩

/-- A nonzero concrete theorem-4.9 target can be represented by a genuinely nonzero raw
Definition 4.8 generator-family combination.  In particular, the coefficient support is nonempty;
the nonempty term-set theorem alone only says that the chosen ambient finite set is nonempty. -/
theorem Theorem49BoundaryRootSynthesis.exists_nonzero_rawGeneratorSum_and_nonempty_coeffSupport_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (z : theorem49BoundaryZeroKirchhoffSubspace emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (hz : z ≠ 0) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (p : G.edgeSet → Color),
      terms.Nonempty ∧
        coeff.support.Nonempty ∧
          (terms : Set (G.edgeSet → Color)) ⊆
              kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
            coeff.support ⊆ terms ∧
              (∑ y ∈ terms, coeff y • y) ∈
                  kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                (∑ y ∈ terms, coeff y • y) ≠ 0 ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) =
                    (z : G.edgeSet → Color) ∧
                  p ∈ projectedKempeClosureGeneratorSubspace emb C₀ ∧
                    p ≠ 0 ∧
                      chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  rcases
    h.exists_nonempty_rawGeneratorSum_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
      z hz with
    ⟨coeff, terms, p, htermsNonempty, hterms, hsupport, hkirch, hproj, hp,
      hpNonzero, hpair⟩
  let raw : G.edgeSet → Color := ∑ y ∈ terms, coeff y • y
  have hrawNonzero : raw ≠ 0 := by
    intro hrawZero
    apply hz
    apply Subtype.ext
    simpa [raw, hrawZero] using hproj.symm
  have hcoeffSupportNonempty : coeff.support.Nonempty := by
    have hcoeffNonzero : coeff ≠ 0 := by
      intro hcoeffZero
      apply hrawNonzero
      simp [raw, hcoeffZero]
    simpa using (Function.support_nonempty_iff.mpr hcoeffNonzero)
  exact
    ⟨coeff, terms, p, htermsNonempty, hcoeffSupportNonempty, hterms, hsupport, hkirch,
      by simpa [raw] using hrawNonzero, hproj, hp, hpNonzero, hpair⟩

/-- A nonzero concrete theorem-4.9 target has an actual raw Definition 4.8 generator term
appearing with nonzero coefficient in a finite raw representative.  This is the term-level
payload of the support-sensitive non-vacuity theorem: the nonzero coefficient support is not just
abstractly inhabited, but contains a generator-family chain used by the raw representative. -/
theorem Theorem49BoundaryRootSynthesis.exists_rawGenerator_with_nonzero_coeff_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (z : theorem49BoundaryZeroKirchhoffSubspace emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (hz : z ≠ 0) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (y p : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆
          kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          y ∈ coeff.support ∧
            y ∈ terms ∧
              y ∈ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                coeff y ≠ 0 ∧
                  (∑ x ∈ terms, coeff x • x) ∈
                      kirchhoffSubmodule G
                        (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                    (∑ x ∈ terms, coeff x • x) ≠ 0 ∧
                      boundaryZeroProjection
                        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                          (∑ x ∈ terms, coeff x • x) =
                        (z : G.edgeSet → Color) ∧
                      p ∈ projectedKempeClosureGeneratorSubspace emb C₀ ∧
                        p ≠ 0 ∧
                          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  rcases
    h.exists_nonzero_rawGeneratorSum_and_nonempty_coeffSupport_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
      z hz with
    ⟨coeff, terms, p, _htermsNonempty, hcoeffSupportNonempty, hterms, hsupport, hkirch,
      hrawNonzero, hproj, hp, hpNonzero, hpair⟩
  rcases hcoeffSupportNonempty with ⟨y, hySupport⟩
  have hyTerms : y ∈ terms := hsupport hySupport
  have hyFamily : y ∈ kempeClosureGeneratorFamily emb.faceBoundary C₀ := hterms hyTerms
  have hcoeffYNonzero : coeff y ≠ 0 := by
    simpa [Function.mem_support] using hySupport
  exact
    ⟨coeff, terms, y, p, hterms, hsupport, hySupport, hyTerms, hyFamily,
      hcoeffYNonzero, hkirch, hrawNonzero, hproj, hp, hpNonzero, hpair⟩

/-- A nonzero concrete theorem-4.9 target has a nonzero raw Definition 4.8 generator term
appearing with nonzero coefficient in a finite raw representative. This removes the remaining
degeneracy in the term-level witness: the support term is not just formally present, it is a
nonzero chain in the ambient edge-coloring vector space. -/
theorem Theorem49BoundaryRootSynthesis.exists_nonzero_rawGenerator_with_nonzero_coeff_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (z : theorem49BoundaryZeroKirchhoffSubspace emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (hz : z ≠ 0) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (y p : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆
          kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          y ∈ coeff.support ∧
            y ∈ terms ∧
              y ∈ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                y ≠ 0 ∧
                  coeff y ≠ 0 ∧
                    (∑ x ∈ terms, coeff x • x) ∈
                        kirchhoffSubmodule G
                          (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                      (∑ x ∈ terms, coeff x • x) ≠ 0 ∧
                        boundaryZeroProjection
                          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                            (∑ x ∈ terms, coeff x • x) =
                          (z : G.edgeSet → Color) ∧
                        p ∈ projectedKempeClosureGeneratorSubspace emb C₀ ∧
                          p ≠ 0 ∧
                            chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  rcases
    h.exists_rawGenerator_with_nonzero_coeff_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
      z hz with
    ⟨coeff, terms, y₀, p, hterms, hsupport, hy₀Support, _hy₀Terms, _hy₀Family,
      _hy₀Coeff, hkirch, hrawNonzero, hproj, hp, hpNonzero, hpair⟩
  have hnonzeroSupport : ∃ y, y ∈ coeff.support ∧ y ≠ 0 := by
    by_contra hnone
    apply hrawNonzero
    refine Finset.sum_eq_zero ?_
    intro x hxTerms
    by_cases hxSupport : x ∈ coeff.support
    · have hxZero : x = 0 := by
        by_contra hxNonzero
        exact hnone ⟨x, hxSupport, hxNonzero⟩
      simp [hxZero]
    · have hcoeffZero : coeff x = 0 := by
        have hcoeffNotNonzero : ¬ coeff x ≠ 0 := by
          simpa [Function.mem_support] using hxSupport
        exact not_ne_iff.mp hcoeffNotNonzero
      simp [hcoeffZero]
  rcases hnonzeroSupport with ⟨y, hySupport, hyNonzero⟩
  have hyTerms : y ∈ terms := hsupport hySupport
  have hyFamily : y ∈ kempeClosureGeneratorFamily emb.faceBoundary C₀ := hterms hyTerms
  have hcoeffYNonzero : coeff y ≠ 0 := by
    simpa [Function.mem_support] using hySupport
  exact
    ⟨coeff, terms, y, p, hterms, hsupport, hySupport, hyTerms, hyFamily, hyNonzero,
      hcoeffYNonzero, hkirch, hrawNonzero, hproj, hp, hpNonzero, hpair⟩

/-- A nonzero concrete theorem-4.9 target has a raw Definition 4.8 generator term whose
selected-boundary erasure is itself nonzero. This is the boundary-facing term-level payload of the
finite raw representative: the nonzero target cannot be produced entirely from support terms that
vanish under `boundaryZeroProjection`. -/
theorem Theorem49BoundaryRootSynthesis.exists_rawGenerator_with_nonzero_boundaryZeroProjection_and_nonzero_coeff_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {C₀ : G.EdgeColoring Color}
    (h : Theorem49BoundaryRootSynthesis emb C₀)
    (z : theorem49BoundaryZeroKirchhoffSubspace emb
      (selectedBoundaryInteriorEdgeEndpointVertices emb))
    (hz : z ≠ 0) :
    ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
        (y p : G.edgeSet → Color),
      (terms : Set (G.edgeSet → Color)) ⊆
          kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
        coeff.support ⊆ terms ∧
          y ∈ coeff.support ∧
            y ∈ terms ∧
              y ∈ kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
                boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y ≠ 0 ∧
                  y ≠ 0 ∧
                    coeff y ≠ 0 ∧
                      (∑ x ∈ terms, coeff x • x) ∈
                          kirchhoffSubmodule G
                            (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                        (∑ x ∈ terms, coeff x • x) ≠ 0 ∧
                          boundaryZeroProjection
                            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                              (∑ x ∈ terms, coeff x • x) =
                            (z : G.edgeSet → Color) ∧
                          p ∈ projectedKempeClosureGeneratorSubspace emb C₀ ∧
                            p ≠ 0 ∧
                              chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) ≠ 0 := by
  rcases
    h.exists_nonzero_rawGenerator_with_nonzero_coeff_and_nonzero_projectedGenerator_chainDot_ne_zero_of_ne_zero_mem_theorem49BoundaryZeroKirchhoffSubspace
      z hz with
    ⟨coeff, terms, _y₀, p, hterms, hsupport, _hy₀Support, _hy₀Terms, _hy₀Family,
      _hy₀Nonzero, _hy₀Coeff, hkirch, hrawNonzero, hproj, hp, hpNonzero, hpair⟩
  have hnonzeroBoundarySupport :
      ∃ y, y ∈ coeff.support ∧
        boundaryZeroProjection
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y ≠ 0 := by
    by_contra hnone
    have hprojRawZero :
        boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
            (∑ x ∈ terms, coeff x • x) = 0 := by
      calc
        boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
            (∑ x ∈ terms, coeff x • x) =
            ∑ x ∈ terms,
              coeff x •
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
          simp
        _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro x hxTerms
          by_cases hxSupport : x ∈ coeff.support
          · have hxProjZero :
                boundaryZeroProjection
                  (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x = 0 := by
              by_contra hxProjNonzero
              exact hnone ⟨x, hxSupport, hxProjNonzero⟩
            simp [hxProjZero]
          · have hcoeffZero : coeff x = 0 := by
              have hcoeffNotNonzero : ¬ coeff x ≠ 0 := by
                simpa [Function.mem_support] using hxSupport
              exact not_ne_iff.mp hcoeffNotNonzero
            simp [hcoeffZero]
    have hzVectorZero : (z : G.edgeSet → Color) = 0 := by
      simpa [hproj] using hprojRawZero
    exact hz (Subtype.ext hzVectorZero)
  rcases hnonzeroBoundarySupport with ⟨y, hySupport, hyProjectionNonzero⟩
  have hyTerms : y ∈ terms := hsupport hySupport
  have hyFamily : y ∈ kempeClosureGeneratorFamily emb.faceBoundary C₀ := hterms hyTerms
  have hyNonzero : y ≠ 0 := by
    intro hyZero
    apply hyProjectionNonzero
    simp [hyZero]
  have hcoeffYNonzero : coeff y ≠ 0 := by
    simpa [Function.mem_support] using hySupport
  exact
    ⟨coeff, terms, y, p, hterms, hsupport, hySupport, hyTerms, hyFamily,
      hyProjectionNonzero, hyNonzero, hcoeffYNonzero, hkirch, hrawNonzero,
      hproj, hp, hpNonzero, hpair⟩

/-- Outer-boundary-root presentation of the common synthesis package. The outer-root data is an
input theorem surface, but the synthesized consequences depend only on the embedding and the Tait
coloring. -/
abbrev Theorem49OuterBoundaryRootSynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (_data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) : Prop :=
  Theorem49BoundaryRootSynthesis emb C₀

/-- Two-sided annulus-root presentation of the same synthesis package. This is the direct
ground-up synthesis surface for the annulus-root replacement route. -/
abbrev Theorem49AnnulusRootSynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (_data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) : Prop :=
  Theorem49BoundaryRootSynthesis emb C₀

/-- Route-independent synthesis constructor from the single algebraic hypothesis that every
selected-boundary-zero annihilator of the Definition 4.8 family vanishes. All remaining fields of
`Theorem49BoundaryRootSynthesis` are then obtained by the generic projected-source algebra. -/
theorem theorem49BoundaryRootSynthesis_of_boundaryZeroAnnihilatorTrivial
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (C₀ : G.EdgeColoring Color)
    (htrivial : BoundaryZeroAnnihilatorTrivialForEmbedding emb C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  have hboundary :
      ∀ v ∈ selectedBoundaryInteriorEdgeEndpointVertices emb,
        ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces,
          v ∉ (e : Sym2 V) :=
    selectedBoundaryInteriorEdgeEndpointVertices_avoids_selectedBoundarySupport emb
  have htargetLeProjectedGeneratorFamilySpan :
      theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb) ≤
        Submodule.span F2 (projectedKempeClosureGeneratorFamily emb C₀) := by
    rw [span_projectedKempeClosureGeneratorFamily_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
      emb C₀ htrivial]
    exact
      theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
        emb (selectedBoundaryInteriorEdgeEndpointVertices emb)
  have hprojectedGeneratorRepresentation :
      ∀ {z : G.edgeSet → Color},
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb) →
          ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
            (terms : Set (G.edgeSet → Color)) ⊆
                projectedKempeClosureGeneratorFamily emb C₀ ∧
              coeff.support ⊆ terms ∧
                ∑ y ∈ terms, coeff y • y = z := by
    intro z hz
    exact
      exists_projectedKempeClosureGeneratorFamily_finset_sum_of_mem_span_projectedKempeClosureGeneratorFamily
        (htargetLeProjectedGeneratorFamilySpan hz)
  have hrawGeneratorProjectionRepresentation :
      ∀ {z : G.edgeSet → Color},
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb) →
          ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
            (terms : Set (G.edgeSet → Color)) ⊆
                kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
              coeff.support ⊆ terms ∧
                (∑ y ∈ terms, coeff y • y) ∈
                    kirchhoffSubmodule G
                      (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) = z := by
    intro z hz
    rcases
      exists_kempeClosureGeneratorFamily_finset_sum_boundaryZeroProjection_of_mem_projectedKempeClosureGeneratorSubspace
        ((theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_boundaryZeroAnnihilatorTrivial
          emb C₀ htrivial (selectedBoundaryInteriorEdgeEndpointVertices emb)) hz) with
      ⟨coeff, terms, hterms, hsupport, hproj⟩
    refine ⟨coeff, terms, hterms, hsupport, ?_, hproj⟩
    have hprojKirch :
        boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
            (∑ y ∈ terms, coeff y • y) ∈
          kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) := by
      rw [hproj]
      exact hz.1
    exact
      (boundaryZeroProjection_mem_kirchhoffSubmodule_iff_of_boundary_avoids_vertices
        (G := G)
        (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
        (vertices := selectedBoundaryInteriorEdgeEndpointVertices emb)
        (x := ∑ y ∈ terms, coeff y • y) hboundary).1 hprojKirch
  have hrawSourcePreimage :
      ∀ {z : G.edgeSet → Color},
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb) →
          ∃ y ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
              kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb),
            boundaryZeroProjection
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) y = z := by
    intro z hz
    rcases hrawGeneratorProjectionRepresentation hz with
      ⟨coeff, terms, hterms, hsupport, hkirch, hproj⟩
    let raw : G.edgeSet → Color := ∑ y ∈ terms, coeff y • y
    have hrawSpan :
        raw ∈ kempeClosureGeneratorSubspace emb.faceBoundary C₀ := by
      have hrawSpan' :
          raw ∈ Submodule.span F2 (kempeClosureGeneratorFamily emb.faceBoundary C₀) :=
        (Submodule.mem_span_iff_exists_finset_subset
          (R := F2) (s := kempeClosureGeneratorFamily emb.faceBoundary C₀) (x := raw)).2
          ⟨coeff, terms, hterms, hsupport, rfl⟩
      simpa [kempeClosureGeneratorSubspace, raw] using hrawSpan'
    exact ⟨raw, ⟨hrawSpan, hkirch⟩, by simpa [raw] using hproj⟩
  have htargetEqRawSourceImage :
      theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb) =
        Submodule.map
          (boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
          (kempeClosureGeneratorSubspace emb.faceBoundary C₀ ⊓
            kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)) := by
    ext z
    constructor
    · intro hz
      rcases hrawSourcePreimage hz with ⟨y, hy, hyproj⟩
      exact ⟨y, hy, hyproj⟩
    · rintro ⟨y, hy, rfl⟩
      exact
        (boundaryZeroProjection_mem_theorem49BoundaryZeroKirchhoffSubspace_iff_of_selectedBoundary_avoids_vertices
          (G := G) (emb := emb)
          (vertices := selectedBoundaryInteriorEdgeEndpointVertices emb)
          (x := y) hboundary).2 hy.2
  have hrawKirchhoffRepresentative :
      ∀ {x : G.edgeSet → Color},
        x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) →
          ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color)),
            (terms : Set (G.edgeSet → Color)) ⊆
                kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
              coeff.support ⊆ terms ∧
                (∑ y ∈ terms, coeff y • y) ∈
                    kirchhoffSubmodule G
                      (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                  boundaryZeroProjection
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                      (∑ y ∈ terms, coeff y • y) =
                    boundaryZeroProjection
                      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
    intro x hx
    have hz :
        boundaryZeroProjection
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x ∈
          theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb) :=
      (boundaryZeroProjection_mem_theorem49BoundaryZeroKirchhoffSubspace_iff_of_selectedBoundary_avoids_vertices
        (G := G) (emb := emb)
        (vertices := selectedBoundaryInteriorEdgeEndpointVertices emb)
        (x := x) hboundary).2 hx
    exact hrawGeneratorProjectionRepresentation hz
  have hrawBoundaryKernelDecomposition :
      ∀ {x : G.edgeSet → Color},
        x ∈ kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb) →
          ∃ (coeff : (G.edgeSet → Color) → F2) (terms : Finset (G.edgeSet → Color))
              (boundaryError : G.edgeSet → Color),
            (terms : Set (G.edgeSet → Color)) ⊆
                kempeClosureGeneratorFamily emb.faceBoundary C₀ ∧
              coeff.support ⊆ terms ∧
                (∑ y ∈ terms, coeff y • y) ∈
                    kirchhoffSubmodule G
                      (selectedBoundaryInteriorEdgeEndpointVertices emb) ∧
                  boundaryError ∈
                      kirchhoffSubmodule G
                        (selectedBoundaryInteriorEdgeEndpointVertices emb) ⊓
                        LinearMap.ker
                          (boundaryZeroProjection
                            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
                    (∑ y ∈ terms, coeff y • y) + boundaryError = x ∧
                      boundaryZeroProjection
                        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
                          (∑ y ∈ terms, coeff y • y) =
                        boundaryZeroProjection
                          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) x := by
    intro x hx
    rcases hrawKirchhoffRepresentative hx with
      ⟨coeff, terms, hterms, hsupport, hkirch, hproj⟩
    let raw : G.edgeSet → Color := ∑ y ∈ terms, coeff y • y
    refine
      ⟨coeff, terms, raw + x, hterms, hsupport, hkirch, ?_, ?_, ?_⟩
    · constructor
      · exact
          (kirchhoffSubmodule G (selectedBoundaryInteriorEdgeEndpointVertices emb)).add_mem
            hkirch hx
      · exact
          (boundaryZeroProjection_eq_zero_iff_mem_boundarySupportedSubmodule
            (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
            (x := raw + x)).2
            (add_mem_boundarySupportedSubmodule_of_boundaryZeroProjection_eq
              (boundary := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
              (x := x) (y := raw) (by simpa [raw] using hproj))
    · simpa [raw] using chain_add_self_add raw x
    · simpa [raw] using hproj
  have hpointwise :
      ∀ {z : theorem49BoundaryZeroKirchhoffSubspace emb
          (selectedBoundaryInteriorEdgeEndpointVertices emb)},
        (∀ p ∈ projectedKempeClosureGeneratorSubspace emb C₀,
          chainDotBilinForm G.edgeSet p (z : G.edgeSet → Color) = 0) ↔
          z = 0 := by
    intro z
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
        htrivial
          ((z : theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) :
            G.edgeSet → Color)
          hboundaryZero hgen e
    · intro hz p _hp
      rw [hz]
      exact (chainDotBilinForm G.edgeSet p).map_zero
  have hpairingKer :
      LinearMap.ker
          (theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
            (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb)) =
        ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    exact
      (hpointwise (z := z)).1
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
  have hfinrankLe :
      Module.finrank F2
          (theorem49BoundaryZeroKirchhoffSubspace emb
            (selectedBoundaryInteriorEdgeEndpointVertices emb)) ≤
        Module.finrank F2 (projectedKempeClosureGeneratorSubspace emb C₀) := by
    let L :=
      theorem49BoundaryZeroKirchhoffSubspaceProjectedGeneratorPairingMap
        (G := G) emb C₀ (selectedBoundaryInteriorEdgeEndpointVertices emb)
    have hinj : Function.Injective L := (LinearMap.ker_eq_bot).1 hpairingKer
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
  refine
    { target_eq_boundaryProjectionImage := ?_
      pointwise_separation := ?_
      pairing_ker_eq_bot := ?_
      finrank_le_projectedGeneratorSubspace := ?_
      target_eq_projectedGeneratorSource := ?_
      target_le_projectedGeneratorSubspace := ?_
      target_le_projectedGeneratorFamilySpan := ?_
      target_eq_rawSourceImage := ?_
      projectedGeneratorRepresentation := ?_
      rawGeneratorProjectionRepresentation := ?_
      rawSourcePreimage := ?_
      rawKirchhoffRepresentative := ?_
      rawBoundaryKernelDecomposition := ?_ }
  · exact
      theorem49BoundaryZeroKirchhoffSubspace_selectedBoundaryInteriorVertices_eq_map_boundaryZeroProjection_kirchhoffSubmodule
        (G := G) emb (interiorEdgeEndpointSupport emb)
  · intro z
    exact hpointwise (z := z)
  · exact hpairingKer
  · exact hfinrankLe
  · rw [theorem49BoundaryZeroKirchhoffSubspace,
      projectedKempeClosureGeneratorSubspace_eq_planarBoundaryZeroSubmodule_of_boundaryZeroAnnihilatorTrivial
        emb C₀ htrivial]
  · exact
      theorem49BoundaryZeroKirchhoffSubspace_le_projectedKempeClosureGeneratorSubspace_of_boundaryZeroAnnihilatorTrivial
        emb C₀ htrivial
        (selectedBoundaryInteriorEdgeEndpointVertices emb)
  · exact htargetLeProjectedGeneratorFamilySpan
  · exact htargetEqRawSourceImage
  · intro z hz
    exact hprojectedGeneratorRepresentation hz
  · intro z hz
    exact hrawGeneratorProjectionRepresentation hz
  · intro z hz
    exact hrawSourcePreimage hz
  · intro x hx
    exact hrawKirchhoffRepresentative hx
  · intro x hx
    exact hrawBoundaryKernelDecomposition hx

/-- The boundary-aware attached certificate surface already discharges the non-geometric Theorem
4.9 hypothesis: every selected-boundary-zero annihilator of the Definition 4.8 family vanishes. -/
theorem boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V}
    (data : PlanarBoundaryAttachedRootedFacePeelCertificate G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    BoundaryZeroAnnihilatorTrivialForEmbedding data.embedding C₀ := by
  intro z hzeroBoundary hgen e
  exact
    zero_on_allEdges_of_boundary_zero_and_planarBoundaryAttachedRootedFacePeelCertificate_of_annihilatesKempeClosureGeneratorFamily
      (data := data) (C₀ := C₀) (C := C₀) (htait := hC₀)
      (hC := G.mem_edgeKempeClosure_self C₀) (z := z)
      (hzeroBoundary := hzeroBoundary) (hgen := hgen) e

/-- The attached rooted face-peel certificate surface already reaches the full current Theorem 4.9
synthesis package. This isolates the remaining route burden upstream of certificate construction. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (data : PlanarBoundaryAttachedRootedFacePeelCertificate G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis data.embedding C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroAnnihilatorTrivial
    (G := G) (emb := data.embedding) C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryAttachedRootedFacePeelCertificate
      data C₀ hC₀)

/-- The boundary-aware height-ordered peel surface already induces the attached rooted
certificate on the same embedding. This pushes the theorem-4.9 synthesis boundary up to the
height-sorted witness-cover interface, with no explicit parent map or annulus decomposition
needed. -/
noncomputable def
    PlanarBoundaryHeightOrderedFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G := by
  exact
    { embedding := emb
      certificate := data.toBoundaryRootedFacePeelCertificate }

/-- The boundary-aware height-ordered peel surface already reaches the full current Theorem 4.9
synthesis package. Once the annulus route produces a height-sorted witness-cover package, no
further theorem-4.9 algebra remains. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  simpa [PlanarBoundaryHeightOrderedFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate] using
    theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
      (G := G)
      (PlanarBoundaryHeightOrderedFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate
        data)
      C₀ hC₀

/-- The finite collar-layer witness-cover surface also already reaches the full current Theorem
4.9 synthesis package, via its canonical height-sorted witness-cover lowering. This moves the
positive route boundary earlier than any explicit remainder bookkeeping. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      (G := G) data.toHeightOrderedFacePeelWitnessData C₀ hC₀

/-- The weakest current boundary-aware well-founded peel witness surface already reaches the full
Theorem 4.9 synthesis package, via the attached rooted certificate it canonically induces. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryWellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryWellFoundedFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
    (G := G) data.toPlanarBoundaryAttachedRootedFacePeelCertificate C₀ hC₀

/-- The weakest explicit-remainder annulus peel surface already induces the boundary-aware
attached rooted certificate on the same embedding. This keeps the synthesis boundary at the
earliest current annulus layer that still carries explicit later-witness remainder geometry. -/
noncomputable def
    PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G := by
  let cert :
      BoundaryRootedFacePeelCertificate emb.faces.attach
        (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) :=
    LocalRemainderBoundaryCollarLayerFacePeelWitnessData.toBoundaryRootedFacePeelCertificate
      (data := data)
  exact
    { embedding := emb
      certificate := cert }

/-- The split annulus decomposition plus witness-assignment surface already induces the
boundary-aware attached rooted certificate, via the canonical local explicit-remainder collar
package it determines. -/
noncomputable def PlanarBoundaryAnnulusWitnessAssignment.toPlanarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    {decomp : PlanarBoundaryAnnulusDecomposition emb}
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp) :
    PlanarBoundaryAttachedRootedFacePeelCertificate G :=
  Mettapedia.GraphTheory.FourColor.PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate
    (data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData)

/-- The weakest explicit-remainder annulus peel surface already reaches the full current
Theorem 4.9 synthesis package. Once this local remainder geometry exists, no further theorem-4.9
algebra remains. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  simpa [Mettapedia.GraphTheory.FourColor.PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate] using
    theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
      (G := G)
      (Mettapedia.GraphTheory.FourColor.PlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData.toPlanarBoundaryAttachedRootedFacePeelCertificate
        data)
      C₀ hC₀

/-- The split annulus decomposition plus witness-assignment surface already reaches the full
current Theorem 4.9 synthesis package. This is the earliest current point where the remaining
burden is purely geometric ownership of witness edges on a fixed annulus decomposition. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    {decomp : PlanarBoundaryAnnulusDecomposition emb}
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact
    theorem49BoundaryRootSynthesis_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      (G := G) data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData C₀ hC₀

/-- Even the weaker annulus collar geometry surface already reaches the full current Theorem 4.9
synthesis package. The remaining burden is purely geometric: once the collar-layer witness data
exists, the attached boundary-rooted certificate and all downstream algebra are automatic. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
    (G := G) data.toPlanarBoundaryAttachedRootedFacePeelCertificate C₀ hC₀

/-- The repaired previous-boundary witness geometry surface also reaches the full synthesis
package, but this is now just a specialization of the weaker collar-geometry route. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusCollarGeometry
    (G := G) data.toPlanarBoundaryAnnulusCollarGeometry C₀ hC₀

/-- Construct the route-level synthesis package from generic boundary-root interior-dual data.
This is the ground-up core behind both the outer-boundary-rooted and the new two-sided annulus-
rooted Theorem 4.9 synthesis surfaces. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroAnnihilatorTrivial
    (G := G) (emb := emb) C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      emb data C₀ hC₀)

/-- Construct the route-level synthesis package from the canonical parent form of generic
boundary-root interior-dual data. This exposes the acyclic-parent sufficiency branch at the same
Theorem 4.9 synthesis layer as the older adjacency-distance package. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryInteriorDualBoundaryRootParentPeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  simpa [planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualBoundaryRootParentPeelData]
    using
      theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
        (G := G)
        (planarBoundaryAttachedRootedFacePeelCertificate_of_interiorDualBoundaryRootParentPeelData
          emb data)
        C₀ hC₀

/-- Construct the outer-boundary-root synthesis package from concrete outer-boundary-rooted
annulus data. -/
theorem theorem49OuterBoundaryRootSynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49OuterBoundaryRootSynthesis emb data C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) data.interiorData C₀ hC₀

/-- Construct the two-sided annulus-root synthesis package directly from annulus-root data. -/
theorem theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49AnnulusRootSynthesis emb data C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) data.interiorData C₀ hC₀

/-- Construct the route-level synthesis package directly from the two-sided annulus-root parent
package.  The annulus boundary split is additional route structure, but the proved algebraic
endpoint still depends only on the embedded parent payload. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
    (G := G) data.interiorData C₀ hC₀

/-- Same-embedding synthesis constructor from an explicit annulus boundary split and the generic
boundary-root interior-dual adjacency-distance data. This is the primitive two-sided annulus
entry point before packaging the full annulus-root route object. -/
theorem
    theorem49AnnulusRootSynthesis_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49AnnulusRootSynthesis emb
        (planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData interiorData)
        C₀ :=
  theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
    (G := G)
    (planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData)
    C₀ hC₀

/-- Same-embedding synthesis constructor from an explicit annulus boundary split and the generic
boundary-root interior-dual parent data. This is the primitive two-sided annulus entry point for
the acyclic-parent sufficiency branch. -/
theorem
    theorem49BoundaryRootSynthesis_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusRootParentPeelData
    (G := G)
    (planarBoundaryAnnulusRootParentPeelData_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
      boundaryData interiorData)
    C₀ hC₀

/-- Closed-walk source constructor for the acyclic-parent sufficiency branch at the proved
Theorem 4.9 synthesis endpoint. -/
theorem
    theorem49BoundaryRootSynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusRootParentPeelData
    (G := G)
    (planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
      source interiorData)
    C₀ hC₀

/-- Direct synthesis constructor from annulus-construction data plus the explicit parent-witness
orientation hypothesis. This bypasses the older interior-dual boundary-root packaging and uses the
construction-side annihilator route directly on the selected-boundary purified endpoint carrier. -/
theorem theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusConstruction_of_parentWitness
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hparentWitness : data.ParentWitnessOrientation)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_boundaryZeroAnnihilatorTrivial
    (G := G) (emb := emb) C₀
    (boundaryZeroAnnihilatorTrivialForEmbedding_of_planarBoundaryAnnulusConstruction_of_parentWitness
      emb data hparentWitness C₀ hC₀)

/-- Graph-level synthesis theorem for the attached rooted face-peel certificate route. Once any
graph reaches this certificate surface, the remaining Theorem 4.9 algebra is automatic. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAttachedRootedFacePeelCertificate
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨data⟩
  exact ⟨data.embedding,
    theorem49BoundaryRootSynthesis_of_planarBoundaryAttachedRootedFacePeelCertificate
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the boundary-aware height-ordered witness-cover surface.
This shows the current theorem-4.9 endpoint already starts at the height-sorted annulus peeling
interface. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryHeightOrderedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryHeightOrderedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryHeightOrderedFacePeelWitnessData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the finite collar-layer witness-cover surface. This moves
the theorem-4.9 boundary earlier than any explicit annulus-remainder package. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryCollarLayerFacePeelWitnessData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the weakest current boundary-aware well-founded peel
witness surface. This packages the canonical certificate conversion before invoking the generic
synthesis endpoint. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryWellFoundedFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryWellFoundedFacePeelWitnessData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the weakest local explicit-remainder annulus peel surface.
Once a graph reaches this annulus-side remainder geometry, theorem-4.9 synthesis is automatic. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the split annulus decomposition plus witness-assignment
surface. This isolates the remaining theorem-4.9 burden at the current pure annulus geometry plus
witness-ownership layer. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAnnulusWitnessAssignment
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAnnulusWitnessAssignment G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, _decomp, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusWitnessAssignment
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the collar-geometry route. This packages the fact that the
weaker annulus collar witness data already contains enough structure to induce the boundary-aware
certificate surface. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAnnulusCollarGeometry G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAttachedRootedFacePeelCertificate
    (admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryAnnulusCollarGeometry
      hG)
    C₀ hC₀

/-- Graph-level synthesis theorem for the corrected previous-boundary witness geometry surface.
This now factors through the weaker collar-geometry route because the synthesis burden itself no
longer depends on the previous-boundary witness placement refinement. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAnnulusCollarGeometry
    (admitsPlanarBoundaryAnnulusCollarGeometry_of_admitsPlanarBoundaryAnnulusPreviousBoundaryWitnessGeometry
      hG)
    C₀ hC₀

/-- Synthesis theorem for the repaired collar-geometry surface stated directly with the explicit
current-boundary witness placement witness. This isolates the live geometric content without
restating certificate or well-founded-peeling intermediates. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusCollarGeometry emb,
        data.WitnessOnCurrentBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAttachedRootedFacePeelCertificate
    (admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_exists_planarBoundaryAnnulusCollarGeometry_and_witnessOnCurrentBoundary
      hG)
    C₀ hC₀

/-- The annulus-construction parent-witness orientation surface already reaches the boundary-aware
attached certificate endpoint via the canonical well-founded peel witness. -/
theorem admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation G) :
    AdmitsPlanarBoundaryAttachedRootedFacePeelCertificate G := by
  exact
    admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryWellFoundedFacePeelWitnessData
      (admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
        hG)

/-- Graph-level synthesis theorem for the construction-side parent-witness annulus route. This is
the current ground-up entry point from explicit annulus-construction geometry into the full
Theorem 4.9 synthesis package. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ :=
  exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAttachedRootedFacePeelCertificate
    (admitsPlanarBoundaryAttachedRootedFacePeelCertificate_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
      hG)
    C₀ hC₀

/-- Graph-level ground-up synthesis theorem for the generic boundary-root interior-dual route. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level ground-up synthesis theorem for the canonical-parent boundary-root interior-dual
route. This is the end-to-end synthesis endpoint for source arguments that construct an acyclic
parent witness instead of an adjacency-distance package. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the current outer-boundary-rooted Theorem 4.9 route. -/
theorem exists_theorem49OuterBoundaryRootSynthesis_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        Theorem49OuterBoundaryRootSynthesis emb data C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49OuterBoundaryRootSynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the two-sided annulus-root Theorem 4.9 route. -/
theorem exists_theorem49AnnulusRootSynthesis_of_admitsPlanarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootSynthesis emb data C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, data,
    theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem for the two-sided annulus-root parent route.  This packages the
annulus-side boundary split together with the acyclic-parent payload before invoking the generic
Theorem 4.9 endpoint. -/
theorem exists_theorem49BoundaryRootSynthesis_of_admitsPlanarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : AdmitsPlanarBoundaryAnnulusRootParentPeelData G)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusRootParentPeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem from an explicit annulus boundary split plus generic
boundary-root interior-dual data on the same embedding. This exposes the theorem-4.9 endpoint
at the primitive two-sided annulus-split layer, before any stronger closed-walk source fields are
introduced. -/
theorem
    exists_theorem49AnnulusRootSynthesis_of_exists_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootSynthesis emb data C₀ := by
  rcases hG with ⟨emb, boundaryData, ⟨interiorData⟩⟩
  let data :=
    planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData
  exact ⟨emb, data,
    theorem49AnnulusRootSynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := G) data C₀ hC₀⟩

/-- Graph-level synthesis theorem from an explicit annulus boundary split plus generic
boundary-root parent data on the same embedding. This is the primitive two-sided annulus-split
entry point for the parent-oriented theorem-4.9 route. -/
theorem
    exists_theorem49BoundaryRootSynthesis_of_exists_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
        Nonempty (InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary))
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases hG with ⟨emb, boundaryData, ⟨interiorData⟩⟩
  exact ⟨emb,
    theorem49BoundaryRootSynthesis_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
      (G := G) boundaryData interiorData C₀ hC₀⟩

/-- Non-vacuous version of the common Theorem 4.9 synthesis endpoint. This deliberately does not
change the algebraic package: it records the additional route obligation that the selected-
boundary purified interior-edge endpoint carrier actually contains a vertex. -/
structure Theorem49BoundaryRootNonemptySynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (C₀ : G.EdgeColoring Color) : Prop where
  synthesis : Theorem49BoundaryRootSynthesis emb C₀
  carrier_nonempty : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty

/-- Outer-boundary-root presentation of the non-vacuous synthesis package. -/
abbrev Theorem49OuterBoundaryRootNonemptySynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (_data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) : Prop :=
  Theorem49BoundaryRootNonemptySynthesis emb C₀

/-- Two-sided annulus-root presentation of the non-vacuous synthesis package. -/
abbrev Theorem49AnnulusRootNonemptySynthesis {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G)
    (_data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) : Prop :=
  Theorem49BoundaryRootNonemptySynthesis emb C₀

/-- Construct the non-vacuous synthesis package from generic boundary-root interior-dual data
when the selected-boundary purified carrier is known to be nonempty. -/
theorem theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptySynthesis emb C₀ where
  synthesis :=
    theorem49BoundaryRootSynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀
  carrier_nonempty := hCarrier

/-- Construct the non-vacuous outer-boundary-root synthesis package when the selected-boundary
purified carrier is known to be nonempty. -/
theorem theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49OuterBoundaryRootNonemptySynthesis emb data C₀ :=
  theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) data.interiorData C₀ hC₀ hCarrier

/-- Endpoint-separated outer-boundary-rooted annulus data yields the non-vacuous synthesis
package as soon as the raw interior-edge endpoint carrier is nonempty. The endpoint-separation
field makes selected-boundary purification lossless, so no extra carrier hypothesis is needed
beyond nonemptiness of the raw carrier itself. -/
theorem
    theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49OuterBoundaryRootNonemptySynthesis emb data.routeData C₀ := by
  have hEq :=
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation.selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport
      data
  have hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
    rcases hRawCarrier with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa [hEq] using hv
  exact theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    (G := G) data.routeData C₀ hC₀ hCarrier

/-- Construction-level peeled-face endpoint no-touch is enough to reach the non-vacuous
outer-boundary-root synthesis endpoint once the raw interior-edge endpoint carrier is nonempty.
This packages the new endpoint-separation repair without forcing downstream route theorems to
manually rebuild `WithEndpointSeparation`. -/
theorem
    theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
        data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49OuterBoundaryRootNonemptySynthesis emb data C₀ := by
  exact
    theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
      (G := G)
      (data.withEndpointSeparationOfPeelFacesEndpointDisjoint hPeelNoTouch)
      C₀ hC₀ hRawCarrier

/-- Construct the non-vacuous two-sided annulus-root synthesis package when the selected-boundary
purified carrier is known to be nonempty. -/
theorem theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49AnnulusRootNonemptySynthesis emb data C₀ :=
  theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (G := G) data.interiorData C₀ hC₀ hCarrier

/-- Construct the non-vacuous synthesis package directly from the two-sided annulus-root parent
package when the selected-boundary purified carrier is known to be nonempty. -/
theorem theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptySynthesis emb C₀ where
  synthesis :=
    theorem49BoundaryRootSynthesis_of_planarBoundaryAnnulusRootParentPeelData
      (G := G) data C₀ hC₀
  carrier_nonempty := hCarrier

/-- Two-sided annulus-root data yields the non-vacuous synthesis endpoint as soon as the raw
interior-edge endpoint carrier is nonempty and endpoint-disjoint from the selected boundary.
Unlike the outer-root repair line, this formulation stays on the honest two-sided root surface
and therefore avoids any all-roots-on-one-boundary hypothesis. -/
theorem theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_of_endpointSupport_disjoint
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hEndpointDisjoint : Disjoint (interiorEdgeEndpointSupport emb)
      (edgeEndpointSupport
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  have hEq :
      selectedBoundaryInteriorEdgeEndpointVertices emb =
        interiorEdgeEndpointSupport emb :=
    (selectedBoundaryInteriorEdgeEndpointVertices_eq_interiorEdgeEndpointSupport_iff_endpointSupport_disjoint
      emb).2 hEndpointDisjoint
  have hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
    rcases hRawCarrier with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa [hEq] using hv
  exact
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hCarrier

/-- Construction-level peeled-face endpoint no-touch is enough to reach the non-vacuous
two-sided annulus-root synthesis endpoint once the raw interior-edge endpoint carrier is
nonempty.  This is the generic annulus-root version of the source-facing repair: it avoids the
all-outer-root localization while still making the global endpoint-separation burden explicit as
a local construction condition. -/
theorem
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hPeelNoTouch : ∀ f ∈
      (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootAdjDistancePeelData
        data).peelFaces,
      Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)))
    (hRawCarrier : (interiorEdgeEndpointSupport emb).Nonempty) :
    Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  have hEndpointDisjoint :
      Disjoint (interiorEdgeEndpointSupport emb)
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) :=
    data.endpointSupport_disjoint_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      hPeelNoTouch
  exact
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_of_endpointSupport_disjoint
      (G := G) data C₀ hC₀ hEndpointDisjoint hRawCarrier

/-- Same-embedding non-vacuous synthesis constructor from an explicit annulus boundary split and
generic boundary-root interior-dual data, provided the selected-boundary purified carrier is
nonempty. -/
theorem
    theorem49AnnulusRootNonemptySynthesis_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49AnnulusRootNonemptySynthesis emb
        (planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData interiorData)
        C₀ :=
  theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
    (G := G)
    (planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData)
    C₀ hC₀ hCarrier

/-- Same-embedding non-vacuous synthesis constructor from an explicit annulus boundary split and
generic boundary-root interior-dual parent data, provided the selected-boundary purified carrier
is nonempty. -/
theorem
    theorem49BoundaryRootNonemptySynthesis_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptySynthesis emb C₀ :=
  theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryAnnulusRootParentPeelData
    (G := G)
    (planarBoundaryAnnulusRootParentPeelData_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
      boundaryData interiorData)
    C₀ hC₀ hCarrier

/-- Same-embedding non-vacuous synthesis constructor from an honest closed-walk source and
generic boundary-root interior-dual parent data. -/
theorem
    theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀)
    (hCarrier : (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty) :
    Theorem49BoundaryRootNonemptySynthesis emb C₀ :=
  theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryAnnulusRootParentPeelData
    (G := G)
    (planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
      source interiorData)
    C₀ hC₀ hCarrier

/-- Graph-level non-vacuous synthesis from explicit outer-boundary-rooted annulus data whose
selected-boundary purified endpoint carrier is nonempty. -/
theorem
    exists_theorem49OuterBoundaryRootNonemptySynthesis_of_exists_planarBoundaryOuterBoundaryRootAdjDistancePeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        Theorem49OuterBoundaryRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, data, hCarrier⟩
  exact ⟨emb, data,
    theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hCarrier⟩

/-- Graph-level non-vacuous synthesis from endpoint-separated outer-boundary-rooted annulus data
whose raw interior-edge endpoint carrier is nonempty. This is the current positive repair line
that the endpoint-touch obstruction fails exactly because it cannot satisfy the endpoint-separation
field. -/
theorem
    exists_theorem49OuterBoundaryRootNonemptySynthesis_of_exists_planarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation_with_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data :
        PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation emb,
        (interiorEdgeEndpointSupport emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data :
        PlanarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation emb,
        Theorem49OuterBoundaryRootNonemptySynthesis emb data.routeData C₀ := by
  rcases hG with ⟨emb, data, hRawCarrier⟩
  exact ⟨emb, data,
    theorem49OuterBoundaryRootNonemptySynthesis_of_planarBoundaryOuterBoundaryRootAdjDistancePeelDataWithEndpointSeparation
      (G := G) data C₀ hC₀ hRawCarrier⟩

/-- Graph-level non-vacuous synthesis from explicit two-sided annulus-root data whose selected-
boundary purified endpoint carrier is nonempty. -/
theorem
    exists_theorem49AnnulusRootNonemptySynthesis_of_exists_planarBoundaryAnnulusRootAdjDistancePeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, data, hCarrier⟩
  exact ⟨emb, data,
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hCarrier⟩

/-- Graph-level non-vacuous synthesis from explicit two-sided annulus-root data whose raw
interior-edge endpoint carrier is nonempty and endpoint-disjoint from the selected boundary. -/
theorem
    exists_theorem49AnnulusRootNonemptySynthesis_of_exists_planarBoundaryAnnulusRootAdjDistancePeelData_with_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        (interiorEdgeEndpointSupport emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, data, hEndpointDisjoint, hRawCarrier⟩
  exact ⟨emb, data,
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_of_endpointSupport_disjoint
      (G := G) data C₀ hC₀ hEndpointDisjoint hRawCarrier⟩

/-- Graph-level non-vacuous synthesis from explicit two-sided annulus-root data whose raw
interior-edge endpoint carrier is nonempty and whose canonical construction satisfies peeled-face
endpoint no-touch. -/
theorem
    exists_theorem49AnnulusRootNonemptySynthesis_of_exists_planarBoundaryAnnulusRootAdjDistancePeelData_with_peelFaces_endpoint_disjoint_selectedBoundarySupport_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        (∀ f ∈
          (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootAdjDistancePeelData
            data).peelFaces,
          Disjoint (edgeEndpointSupport (emb.faceBoundary f.1))
            (edgeEndpointSupport
              (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))) ∧
        (interiorEdgeEndpointSupport emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, data, hPeelNoTouch, hRawCarrier⟩
  exact ⟨emb, data,
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData_of_peelFaces_endpoint_disjoint_selectedBoundarySupport
      (G := G) data C₀ hC₀ hPeelNoTouch hRawCarrier⟩

/-- Graph-level non-vacuous synthesis theorem from an explicit annulus boundary split plus
generic boundary-root interior-dual data on the same embedding. This is the primitive two-sided
annulus entry point when a nonempty selected-boundary purified carrier is available. -/
theorem
    exists_theorem49AnnulusRootNonemptySynthesis_of_exists_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
      ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb,
        Theorem49AnnulusRootNonemptySynthesis emb data C₀ := by
  rcases hG with ⟨emb, boundaryData, interiorData, hCarrier⟩
  let data :=
    planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData
  exact ⟨emb, data,
    theorem49AnnulusRootNonemptySynthesis_of_planarBoundaryAnnulusRootAdjDistancePeelData
      (G := G) data C₀ hC₀ hCarrier⟩

/-- Graph-level non-vacuous synthesis from explicit two-sided annulus-root parent data whose
selected-boundary purified endpoint carrier is nonempty. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_planarBoundaryAnnulusRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _data : PlanarBoundaryAnnulusRootParentPeelData emb,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with ⟨emb, data, hCarrier⟩
  exact ⟨emb,
    theorem49BoundaryRootNonemptySynthesis_of_planarBoundaryAnnulusRootParentPeelData
      (G := G) data C₀ hC₀ hCarrier⟩

/-- Graph-level non-vacuous synthesis theorem from an explicit annulus boundary split plus
generic boundary-root interior-dual parent data on the same embedding. This is the primitive
two-sided annulus entry point for the parent-oriented branch when a nonempty selected-boundary
purified carrier is available. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_boundaryData_and_interiorDualBoundaryRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with ⟨emb, boundaryData, interiorData, hCarrier⟩
  exact ⟨emb,
    theorem49BoundaryRootNonemptySynthesis_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
      (G := G) boundaryData interiorData C₀ hC₀ hCarrier⟩

/-- Graph-level non-vacuous synthesis theorem from an honest closed-walk source plus generic
boundary-root interior-dual parent data on the same embedding. -/
theorem
    exists_theorem49BoundaryRootNonemptySynthesis_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData_with_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary,
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty)
    (C₀ : G.EdgeColoring Color) (hC₀ : IsTaitEdgeColoring G C₀) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      Theorem49BoundaryRootNonemptySynthesis emb C₀ := by
  rcases hG with ⟨emb, source, interiorData, hCarrier⟩
  exact ⟨emb,
    theorem49BoundaryRootNonemptySynthesis_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
      (G := G) source interiorData C₀ hC₀ hCarrier⟩

end Mettapedia.GraphTheory.FourColor
