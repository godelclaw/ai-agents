import Mettapedia.GraphTheory.FourColor.PlanarBoundaryOrderedEmbedding
import Mettapedia.GraphTheory.FourColor.Theorem49RootedDistance

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Concrete annulus-boundary witness data from the current embedding API: two distinguished
boundary edges together with the claim that every ambient boundary edge lies in exactly one
reachability component of the shared-endpoint boundary graph. This is stronger and more geometric
than an arbitrary outer/inner partition, but still expressible without full cyclic-order
topology. -/
structure PlanarBoundaryAnnulusBoundaryReachabilityData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  outerRoot : PlanarBoundaryEdgeVertex emb
  innerRoot : PlanarBoundaryEdgeVertex emb
  hroots_ne : outerRoot ≠ innerRoot
  hcoverRoots :
    RootSetCovers (planarBoundarySupportEndpointAdjGraph emb)
      ({outerRoot, innerRoot} : Finset (PlanarBoundaryEdgeVertex emb))
  hsepRoots :
    RootSetSeparated (planarBoundarySupportEndpointAdjGraph emb)
      ({outerRoot, innerRoot} : Finset (PlanarBoundaryEdgeVertex emb))

/-- The two distinguished boundary-component roots as a finite root set for the shared-endpoint
boundary graph. -/
def PlanarBoundaryAnnulusBoundaryReachabilityData.rootSet
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb) :
    Finset (PlanarBoundaryEdgeVertex emb) :=
  {data.outerRoot, data.innerRoot}

/-- The cover/separation witness on the two distinguished boundary roots upgrades to the canonical
unique-root package on the shared-endpoint boundary graph. -/
noncomputable def PlanarBoundaryAnnulusBoundaryReachabilityData.hasUniqueReachableRoot
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb) :
    HasUniqueReachableRoot (planarBoundarySupportEndpointAdjGraph emb) data.rootSet :=
  hasUniqueReachableRoot_of_cover_and_separated
    (planarBoundarySupportEndpointAdjGraph emb) data.rootSet data.hcoverRoots data.hsepRoots

/-- Graph-level existence form of the shared-endpoint boundary-component witness. -/
def AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb)

/-- A concrete shared-endpoint boundary-component witness canonically yields the abstract annulus
boundary split used by the current Step 2 shell. The outer and inner supports are extracted by
filtering boundary edges according to their unique reachable root in the shared-endpoint boundary
graph. -/
noncomputable def
    PlanarBoundaryAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb) :
    PlanarBoundaryAnnulusBoundaryData emb := by
  classical
  let support := selectedBoundarySupport emb.faceBoundary emb.faces emb.faces
  let T := planarBoundarySupportEndpointAdjGraph emb
  let roots := data.rootSet
  let hroots := data.hasUniqueReachableRoot
  let outerVerts :=
    support.attach.filter fun e => uniqueReachableRoot T roots hroots e = data.outerRoot
  let innerVerts :=
    support.attach.filter fun e => uniqueReachableRoot T roots hroots e = data.innerRoot
  refine
    { outerAmbientBoundary := outerVerts.image Subtype.val
      innerAmbientBoundary := innerVerts.image Subtype.val
      houterAmbientBoundaryNonempty := ?_
      hinnerAmbientBoundaryNonempty := ?_
      houterAmbientBoundarySubset := ?_
      hinnerAmbientBoundarySubset := ?_
      hambientBoundaryCover := ?_
      hambientBoundaryDisjoint := ?_ }
  · refine ⟨data.outerRoot.1, Finset.mem_image.2 ?_⟩
    refine ⟨data.outerRoot, Finset.mem_filter.2 ⟨by simp, ?_⟩, rfl⟩
    apply (hroots data.outerRoot).unique
    · exact ⟨uniqueReachableRoot_mem_roots T roots hroots data.outerRoot,
        reachable_uniqueReachableRoot T roots hroots data.outerRoot⟩
    · exact ⟨by
          simp [PlanarBoundaryAnnulusBoundaryReachabilityData.rootSet, data.hroots_ne],
        SimpleGraph.Reachable.refl data.outerRoot⟩
  · refine ⟨data.innerRoot.1, Finset.mem_image.2 ?_⟩
    refine ⟨data.innerRoot, Finset.mem_filter.2 ⟨by simp, ?_⟩, rfl⟩
    apply (hroots data.innerRoot).unique
    · exact ⟨uniqueReachableRoot_mem_roots T roots hroots data.innerRoot,
        reachable_uniqueReachableRoot T roots hroots data.innerRoot⟩
    · exact ⟨by
          simp [PlanarBoundaryAnnulusBoundaryReachabilityData.rootSet],
        SimpleGraph.Reachable.refl data.innerRoot⟩
  · intro e he
    rcases Finset.mem_image.1 he with ⟨x, hx, rfl⟩
    exact x.2
  · intro e he
    rcases Finset.mem_image.1 he with ⟨x, hx, rfl⟩
    exact x.2
  · intro e he
    have hroot_mem : uniqueReachableRoot T roots hroots ⟨e, he⟩ ∈ roots :=
      uniqueReachableRoot_mem_roots T roots hroots ⟨e, he⟩
    have hroot_cases :
        uniqueReachableRoot T roots hroots ⟨e, he⟩ = data.outerRoot ∨
          uniqueReachableRoot T roots hroots ⟨e, he⟩ = data.innerRoot := by
      simpa [roots, PlanarBoundaryAnnulusBoundaryReachabilityData.rootSet, data.hroots_ne] using
        hroot_mem
    rcases hroot_cases with hOuter | hInner
    · exact Finset.mem_union.2 <| Or.inl <| Finset.mem_image.2
        ⟨⟨e, he⟩, Finset.mem_filter.2 ⟨by simp, hOuter⟩, rfl⟩
    · exact Finset.mem_union.2 <| Or.inr <| Finset.mem_image.2
        ⟨⟨e, he⟩, Finset.mem_filter.2 ⟨by simp, hInner⟩, rfl⟩
  · rw [Finset.disjoint_left]
    intro e heOuter heInner
    rcases Finset.mem_image.1 heOuter with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.1 heInner with ⟨y, hy, hyx⟩
    have hxy : x = y := by
      apply Subtype.ext
      exact hyx.symm
    subst hxy
    have hOuterRoot : uniqueReachableRoot T roots hroots x = data.outerRoot :=
      (Finset.mem_filter.1 hx).2
    have hInnerRoot : uniqueReachableRoot T roots hroots x = data.innerRoot := by
      simpa using (Finset.mem_filter.1 hy).2
    exact data.hroots_ne (hOuterRoot.symm.trans hInnerRoot)

theorem PlanarBoundaryAnnulusBoundaryReachabilityData.mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {e : PlanarBoundaryEdgeVertex emb}
    (hroot :
      uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot e = data.outerRoot) :
    e.1 ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary := by
  classical
  unfold PlanarBoundaryAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData
  refine Finset.mem_image.2 ?_
  refine ⟨e, Finset.mem_filter.2 ⟨by simp, ?_⟩, rfl⟩
  simpa [PlanarBoundaryAnnulusBoundaryReachabilityData.rootSet] using hroot

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.uniqueReachableRoot_eq_outerRoot_of_mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {e : PlanarBoundaryEdgeVertex emb}
    (he : e.1 ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) :
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph emb)
        data.rootSet data.hasUniqueReachableRoot e = data.outerRoot := by
  classical
  unfold PlanarBoundaryAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData at he
  rcases Finset.mem_image.1 he with ⟨x, hx, hxe⟩
  have hxeq : x = e := by
    apply Subtype.ext
    exact hxe
  subst hxeq
  exact (Finset.mem_filter.1 hx).2

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.uniqueReachableRoot_eq_innerRoot_of_mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {e : PlanarBoundaryEdgeVertex emb}
    (he : e.1 ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    uniqueReachableRoot
        (planarBoundarySupportEndpointAdjGraph emb)
        data.rootSet data.hasUniqueReachableRoot e = data.innerRoot := by
  classical
  unfold PlanarBoundaryAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData at he
  rcases Finset.mem_image.1 he with ⟨x, hx, hxe⟩
  have hxeq : x = e := by
    apply Subtype.ext
    exact hxe
  subst hxeq
  exact (Finset.mem_filter.1 hx).2

theorem PlanarBoundaryAnnulusBoundaryReachabilityData.mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {e : PlanarBoundaryEdgeVertex emb}
    (hroot :
      uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot e = data.innerRoot) :
    e.1 ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  classical
  unfold PlanarBoundaryAnnulusBoundaryReachabilityData.toPlanarBoundaryAnnulusBoundaryData
  refine Finset.mem_image.2 ?_
  refine ⟨e, Finset.mem_filter.2 ⟨by simp, ?_⟩, rfl⟩
  simpa [PlanarBoundaryAnnulusBoundaryReachabilityData.rootSet] using hroot

/-- Facewise boundary-component coherence for the shared-endpoint annulus boundary model: any two
selected-boundary edges on the same ambient face belong to the same unique boundary component. -/
def PlanarBoundaryAnnulusBoundaryReachabilityData.BoundaryComponentConstantOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (f : AmbientFace emb.faces) : Prop :=
  ∀ ⦃e₁ e₂ : G.edgeSet⦄,
    e₁ ∈ emb.faceBoundary f.1 →
      e₂ ∈ emb.faceBoundary f.1 →
        (he₁ : e₁ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) →
          (he₂ : e₂ ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) →
            uniqueReachableRoot
                (planarBoundarySupportEndpointAdjGraph emb)
                data.rootSet data.hasUniqueReachableRoot ⟨e₁, he₁⟩ =
              uniqueReachableRoot
                (planarBoundarySupportEndpointAdjGraph emb)
                data.rootSet data.hasUniqueReachableRoot ⟨e₂, he₂⟩


theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryComponentConstantOnFace_of_boundaryComponentReachableOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (hreach : BoundaryComponentReachableOnFace (emb := emb) f) :
    data.BoundaryComponentConstantOnFace f := by
  intro e₁ e₂ he₁Face he₂Face he₁ he₂
  exact uniqueReachableRoot_eq_of_reachable
    (planarBoundarySupportEndpointAdjGraph emb)
    data.rootSet data.hasUniqueReachableRoot
    (hreach he₁Face he₂Face he₁ he₂)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryComponentConstantOnFace_of_boundaryComponentWalkOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (hwalk : BoundaryComponentWalkOnFace (emb := emb) f) :
    data.BoundaryComponentConstantOnFace f := by
  exact
    data.boundaryComponentConstantOnFace_of_boundaryComponentReachableOnFace
      (boundaryComponentReachableOnFace_of_boundaryComponentWalkOnFace hwalk)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryComponentConstantOnFace_of_boundaryComponentRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (hrun : BoundaryComponentRunOnFace (emb := emb) f) :
    data.BoundaryComponentConstantOnFace f := by
  exact
    data.boundaryComponentConstantOnFace_of_boundaryComponentReachableOnFace
      (boundaryComponentReachableOnFace_of_boundaryComponentRunOnFace hrun)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryComponentConstantOnFace_of_boundarySelectedBoundaryRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (hrun : BoundarySelectedBoundaryRunOnFace (emb := emb) f) :
    data.BoundaryComponentConstantOnFace f := by
  exact
    data.boundaryComponentConstantOnFace_of_boundaryComponentReachableOnFace
      (boundaryComponentReachableOnFace_of_boundarySelectedBoundaryRunOnFace hrun)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryComponentConstantOnFace_of_boundarySelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (harc : BoundarySelectedBoundaryArcOnFace (emb := emb) f) :
    data.BoundaryComponentConstantOnFace f := by
  exact
    data.boundaryComponentConstantOnFace_of_boundaryComponentReachableOnFace
      (boundaryComponentReachableOnFace_of_boundarySelectedBoundaryArcOnFace harc)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryComponentConstantOnFace_of_selectedBoundaryArcGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb)
    {f : AmbientFace emb.faces} :
    data.BoundaryComponentConstantOnFace f := by
  exact
    data.boundaryComponentConstantOnFace_of_boundaryComponentReachableOnFace
      (geom.boundaryComponentReachableOnFace f)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryComponentConstantOnFace_of_faceBoundaryRunGeometry_and_selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryFaceBoundaryRunGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces, geom.SelectedBoundaryArcOnFace f)
    {f : AmbientFace emb.faces} :
    data.BoundaryComponentConstantOnFace f := by
  exact
    data.boundaryComponentConstantOnFace_of_boundaryComponentReachableOnFace
      (geom.boundaryComponentReachableOnFace harc f)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryComponentConstantOnFace_of_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces,
      (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    {f : AmbientFace emb.faces} :
    data.BoundaryComponentConstantOnFace f := by
  exact
    data.boundaryComponentConstantOnFace_of_faceBoundaryRunGeometry_and_selectedBoundaryArcOnFace
      geom.toPlanarBoundaryFaceBoundaryRunGeometry harc

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryComponentConstantOnFace_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryClosedWalkEmbeddingData emb)
    (harc : ∀ f : AmbientFace emb.faces,
      (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    {f : AmbientFace emb.faces} :
    data.BoundaryComponentConstantOnFace f := by
  exact
    data.boundaryComponentConstantOnFace_of_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace
      geom.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry
      (by
        intro g
        simpa
          [PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry,
            PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry,
            PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicOrderedFaceEmbeddingData,
            PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryFaceBoundaryRunGeometry]
          using harc g)
      (f := f)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryComponentConstantOnFace_of_orderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryOrderedFaceArcEmbeddingData emb)
    {f : AmbientFace emb.faces} :
    data.BoundaryComponentConstantOnFace f := by
  exact
    data.boundaryComponentConstantOnFace_of_boundaryComponentReachableOnFace
      (geom.boundaryComponentReachableOnFace f)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryComponentConstantOnFace_of_cyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb)
    {f : AmbientFace emb.faces} :
    data.BoundaryComponentConstantOnFace f := by
  exact
    data.boundaryComponentConstantOnFace_of_boundaryComponentReachableOnFace
      (geom.boundaryComponentReachableOnFace f)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_boundaryComponentConstantOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (hconst : data.BoundaryComponentConstantOnFace f) :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  intro hmeet
  rcases hmeet with ⟨⟨eOuter, heOuterFace, heOuter⟩, ⟨eInner, heInnerFace, heInner⟩⟩
  have heOuterSel :
      eOuter ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
    data.toPlanarBoundaryAnnulusBoundaryData.houterAmbientBoundarySubset heOuter
  have heInnerSel :
      eInner ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
    data.toPlanarBoundaryAnnulusBoundaryData.hinnerAmbientBoundarySubset heInner
  have hsame :
      uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨eOuter, heOuterSel⟩ =
        uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨eInner, heInnerSel⟩ :=
    hconst heOuterFace heInnerFace heOuterSel heInnerSel
  have hOuterRoot :
      uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨eOuter, heOuterSel⟩ =
        data.outerRoot :=
    data.uniqueReachableRoot_eq_outerRoot_of_mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
      heOuter
  have hInnerRoot :
      uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨eInner, heInnerSel⟩ =
        data.innerRoot :=
    data.uniqueReachableRoot_eq_innerRoot_of_mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
      heInner
  have hRootsEq : data.outerRoot = data.innerRoot := by
    calc
      data.outerRoot =
          uniqueReachableRoot
              (planarBoundarySupportEndpointAdjGraph emb)
              data.rootSet data.hasUniqueReachableRoot ⟨eOuter, heOuterSel⟩ := hOuterRoot.symm
      _ =
          uniqueReachableRoot
              (planarBoundarySupportEndpointAdjGraph emb)
              data.rootSet data.hasUniqueReachableRoot ⟨eInner, heInnerSel⟩ := hsame
      _ = data.innerRoot := hInnerRoot
  exact data.hroots_ne hRootsEq

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData_of_boundaryComponentConstantOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (hconst : data.BoundaryComponentConstantOnFace f)
    {e : G.edgeSet}
    (hef : e ∈ emb.faceBoundary f.1)
    (heSel : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (houter : ∃ eOuter ∈ emb.faceBoundary f.1,
      eOuter ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) :
    e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary := by
  rcases houter with ⟨eOuter, heOuterFace, heOuter⟩
  have heOuterSel :
      eOuter ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
    data.toPlanarBoundaryAnnulusBoundaryData.houterAmbientBoundarySubset heOuter
  have hsame :
      uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨eOuter, heOuterSel⟩ =
        uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨e, heSel⟩ :=
    hconst heOuterFace hef heOuterSel heSel
  have heRoot :
      uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨e, heSel⟩ =
        data.outerRoot := by
    calc
      uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨e, heSel⟩ =
        uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨eOuter, heOuterSel⟩ := hsame.symm
      _ = data.outerRoot :=
        data.uniqueReachableRoot_eq_outerRoot_of_mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
          heOuter
  exact data.mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData heRoot

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData_of_boundaryComponentConstantOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (hconst : data.BoundaryComponentConstantOnFace f)
    {e : G.edgeSet}
    (hef : e ∈ emb.faceBoundary f.1)
    (heSel : e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hinner : ∃ eInner ∈ emb.faceBoundary f.1,
      eInner ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) :
    e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  rcases hinner with ⟨eInner, heInnerFace, heInner⟩
  have heInnerSel :
      eInner ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
    data.toPlanarBoundaryAnnulusBoundaryData.hinnerAmbientBoundarySubset heInner
  have hsame :
      uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨eInner, heInnerSel⟩ =
        uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨e, heSel⟩ :=
    hconst heInnerFace hef heInnerSel heSel
  have heRoot :
      uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨e, heSel⟩ =
        data.innerRoot := by
    calc
      uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨e, heSel⟩ =
        uniqueReachableRoot
          (planarBoundarySupportEndpointAdjGraph emb)
          data.rootSet data.hasUniqueReachableRoot ⟨eInner, heInnerSel⟩ := hsame.symm
      _ = data.innerRoot :=
        data.uniqueReachableRoot_eq_innerRoot_of_mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
          heInner
  exact data.mem_innerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData heRoot

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_boundaryComponentReachableOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (hreach : BoundaryComponentReachableOnFace (emb := emb) f) :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  exact
    data.boundaryFaceSeparated_of_boundaryComponentConstantOnFace
      (data.boundaryComponentConstantOnFace_of_boundaryComponentReachableOnFace hreach)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_boundaryComponentWalkOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (hwalk : BoundaryComponentWalkOnFace (emb := emb) f) :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  exact
    data.boundaryFaceSeparated_of_boundaryComponentReachableOnFace
      (boundaryComponentReachableOnFace_of_boundaryComponentWalkOnFace hwalk)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_boundaryComponentRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (hrun : BoundaryComponentRunOnFace (emb := emb) f) :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  exact
    data.boundaryFaceSeparated_of_boundaryComponentReachableOnFace
      (boundaryComponentReachableOnFace_of_boundaryComponentRunOnFace hrun)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_boundarySelectedBoundaryRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (hrun : BoundarySelectedBoundaryRunOnFace (emb := emb) f) :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  exact
    data.boundaryFaceSeparated_of_boundaryComponentReachableOnFace
      (boundaryComponentReachableOnFace_of_boundarySelectedBoundaryRunOnFace hrun)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_boundarySelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (harc : BoundarySelectedBoundaryArcOnFace (emb := emb) f) :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  exact
    data.boundaryFaceSeparated_of_boundaryComponentReachableOnFace
      (boundaryComponentReachableOnFace_of_boundarySelectedBoundaryArcOnFace harc)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_selectedBoundaryArcGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb)
    {f : AmbientFace emb.faces} :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  exact
    data.boundaryFaceSeparated_of_boundaryComponentReachableOnFace
      (geom.boundaryComponentReachableOnFace f)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_faceBoundaryRunGeometry_and_selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryFaceBoundaryRunGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces, geom.SelectedBoundaryArcOnFace f)
    {f : AmbientFace emb.faces} :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  exact
    data.boundaryFaceSeparated_of_boundaryComponentReachableOnFace
      (geom.boundaryComponentReachableOnFace harc f)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_orderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryOrderedFaceArcEmbeddingData emb)
    {f : AmbientFace emb.faces} :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  exact
    data.boundaryFaceSeparated_of_boundaryComponentReachableOnFace
      (geom.boundaryComponentReachableOnFace f)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_cyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb)
    {f : AmbientFace emb.faces} :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  exact
    data.boundaryFaceSeparated_of_boundaryComponentReachableOnFace
      (geom.boundaryComponentReachableOnFace f)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces,
      (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    {f : AmbientFace emb.faces} :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  exact
    data.boundaryFaceSeparated_of_faceBoundaryRunGeometry_and_selectedBoundaryArcOnFace
      geom.toPlanarBoundaryFaceBoundaryRunGeometry harc

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryClosedWalkEmbeddingData emb)
    (harc : ∀ f : AmbientFace emb.faces,
      (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    {f : AmbientFace emb.faces} :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  exact
    data.boundaryFaceSeparated_of_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace
      geom.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry
      (by
        intro g
        simpa
          [PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry,
            PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry,
            PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicOrderedFaceEmbeddingData,
            PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryFaceBoundaryRunGeometry]
          using harc g)
      (f := f)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.boundaryFaceSeparated_of_boundaryEdgesShareEndpointOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    {f : AmbientFace emb.faces}
    (hshare : BoundaryEdgesShareEndpointOnFace (emb := emb) f) :
    ¬ ((∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) ∧
        (∃ e ∈ emb.faceBoundary f.1,
          e ∈ data.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)) := by
  exact
    data.boundaryFaceSeparated_of_boundaryComponentReachableOnFace
      (boundaryComponentReachableOnFace_of_boundaryEdgesShareEndpointOnFace hshare)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentConstant
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (hconst : ∀ f : AmbientFace emb.faces, data.BoundaryComponentConstantOnFace f) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  rw [Finset.disjoint_left]
  intro f hfOuter hfInner
  exact
    data.boundaryFaceSeparated_of_boundaryComponentConstantOnFace (hconst f)
      ⟨(data.toPlanarBoundaryAnnulusBoundaryData.mem_outerBoundaryFaces_iff).1 hfOuter,
        (data.toPlanarBoundaryAnnulusBoundaryData.mem_innerBoundaryFaces_iff).1 hfInner⟩

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (hreach : ∀ f : AmbientFace emb.faces, BoundaryComponentReachableOnFace (emb := emb) f) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  exact data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentConstant
    (fun f =>
      data.boundaryComponentConstantOnFace_of_boundaryComponentReachableOnFace
        (hreach f))

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentWalkOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (hwalk : ∀ f : AmbientFace emb.faces, BoundaryComponentWalkOnFace (emb := emb) f) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  exact data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
    (fun f =>
      boundaryComponentReachableOnFace_of_boundaryComponentWalkOnFace
        (hwalk f))

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (hrun : ∀ f : AmbientFace emb.faces, BoundaryComponentRunOnFace (emb := emb) f) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  exact data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
    (fun f =>
      boundaryComponentReachableOnFace_of_boundaryComponentRunOnFace
        (hrun f))

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundarySelectedBoundaryRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (hrun : ∀ f : AmbientFace emb.faces, BoundarySelectedBoundaryRunOnFace (emb := emb) f) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  exact data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
    (fun f =>
      boundaryComponentReachableOnFace_of_boundarySelectedBoundaryRunOnFace
        (hrun f))

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundarySelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (harc : ∀ f : AmbientFace emb.faces, BoundarySelectedBoundaryArcOnFace (emb := emb) f) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  exact data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
    (fun f =>
      boundaryComponentReachableOnFace_of_boundarySelectedBoundaryArcOnFace
        (harc f))

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_selectedBoundaryArcGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  exact data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
    geom.boundaryComponentReachableOnFace

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_faceBoundaryRunGeometry_and_selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryFaceBoundaryRunGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces, geom.SelectedBoundaryArcOnFace f) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  exact data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
    (geom.boundaryComponentReachableOnFace harc)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_orderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryOrderedFaceArcEmbeddingData emb) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  exact data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
    geom.boundaryComponentReachableOnFace

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_cyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  exact data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
    geom.boundaryComponentReachableOnFace

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces,
      (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  exact data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_faceBoundaryRunGeometry_and_selectedBoundaryArcOnFace
    geom.toPlanarBoundaryFaceBoundaryRunGeometry harc

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (geom : PlanarBoundaryClosedWalkEmbeddingData emb)
    (harc : ∀ f : AmbientFace emb.faces,
      (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  exact
    data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace
      geom.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry
      (by
        intro g
        simpa
          [PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry,
            PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry,
            PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicOrderedFaceEmbeddingData,
            PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryFaceBoundaryRunGeometry]
          using harc g)

theorem
    PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryEdgesShareEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (hshare : ∀ f : AmbientFace emb.faces, BoundaryEdgesShareEndpointOnFace (emb := emb) f) :
    Disjoint
      data.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces
      data.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
  exact data.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
    (fun f =>
      boundaryComponentReachableOnFace_of_boundaryEdgesShareEndpointOnFace
        (hshare f))

/-- Graph-level lowering from the concrete shared-endpoint boundary-component witness to the
abstract annulus boundary split interface. -/
theorem
    admitsPlanarBoundaryAnnulusBoundaryData_of_admitsPlanarBoundaryAnnulusBoundaryReachabilityData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusBoundaryReachabilityData G) :
    AdmitsPlanarBoundaryAnnulusBoundaryData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryAnnulusBoundaryData⟩⟩

end Mettapedia.GraphTheory.FourColor
