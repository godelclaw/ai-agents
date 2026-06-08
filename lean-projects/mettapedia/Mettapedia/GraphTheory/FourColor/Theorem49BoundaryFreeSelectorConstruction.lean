import Mettapedia.GraphTheory.FourColor.Theorem49ForcingInteriorEdgeObstruction
import Mettapedia.GraphTheory.FourColor.Theorem49CertificateBuilder

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49ForcingInteriorEdgeObstruction

variable {V : Type*} [DecidableEq V]

/-- The finite set of faces selected by a boundary-free incident-face selector. -/
def BoundaryFreeIncidentFaceSelector.peelFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb) :
    Finset (AmbientFace emb.faces) :=
  (interiorEdgeSupport emb.faceBoundary emb.faces).attach.image
    (fun e => selector.faceOf e.1 e.2)

theorem BoundaryFreeIncidentFaceSelector.faceOf_mem_peelFaces {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    selector.faceOf e he ∈ selector.peelFaces := by
  exact Finset.mem_image.2 ⟨⟨e, he⟩, by simp, rfl⟩

theorem BoundaryFreeIncidentFaceSelector.peelFaces_nonempty_of_mem_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    selector.peelFaces.Nonempty := by
  exact ⟨selector.faceOf e he, selector.faceOf_mem_peelFaces he⟩

theorem BoundaryFreeIncidentFaceSelector.peelFaces_nonempty_of_interiorEdgeSupport_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    selector.peelFaces.Nonempty := by
  rcases hInterior with ⟨e, he⟩
  exact selector.peelFaces_nonempty_of_mem_interiorEdgeSupport he

/-- The selector extracted from canonical-parent route data does not introduce any new peeled
faces: its finite image is contained in the parent package's `peelFaces`. -/
theorem boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_peelFaces_subset
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :
    (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data).peelFaces ⊆
      data.peelFaces := by
  intro f hf
  rcases Finset.mem_image.1 hf with ⟨e, _heMem, hface⟩
  rw [← hface]
  exact
    boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_faceOf_mem_peelFaces
      data e.2

/-- Invert the selector on its finite image. Outside the selected image the fallback value is
irrelevant to the construction, because only selected faces are peeled. -/
noncomputable def BoundaryFreeIncidentFaceSelector.selectedWitnessEdge {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (f : AmbientFace emb.faces) : G.edgeSet :=
  if h : ∃ e : G.edgeSet,
      ∃ he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces,
        selector.faceOf e he = f then
    Classical.choose h
  else
    fallbackEdge f

theorem BoundaryFreeIncidentFaceSelector.selectedWitnessEdge_eq_of_faceOf
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    selector.selectedWitnessEdge fallbackEdge (selector.faceOf e he) = e := by
  classical
  let h : ∃ e' : G.edgeSet,
      ∃ he' : e' ∈ interiorEdgeSupport emb.faceBoundary emb.faces,
        selector.faceOf e' he' = selector.faceOf e he := ⟨e, he, rfl⟩
  rw [BoundaryFreeIncidentFaceSelector.selectedWitnessEdge, dif_pos h]
  rcases Classical.choose_spec h with ⟨heChosen, hface⟩
  exact hinjective heChosen he hface

theorem BoundaryFreeIncidentFaceSelector.selectedWitnessEdge_mem_faceBoundary_of_mem_peelFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    {f : AmbientFace emb.faces} (hf : f ∈ selector.peelFaces) :
    selector.selectedWitnessEdge fallbackEdge f ∈ emb.faceBoundary f.1 := by
  classical
  rcases Finset.mem_image.1 hf with ⟨e, _heMem, hface⟩
  let h : ∃ e' : G.edgeSet,
      ∃ he' : e' ∈ interiorEdgeSupport emb.faceBoundary emb.faces,
        selector.faceOf e' he' = f := ⟨e.1, e.2, hface⟩
  rw [BoundaryFreeIncidentFaceSelector.selectedWitnessEdge, dif_pos h]
  rcases Classical.choose_spec h with ⟨heChosen, hchosenFace⟩
  have hmem :=
    selector.edge_mem_faceOf (e := Classical.choose h) heChosen
  simpa [hchosenFace] using hmem

theorem BoundaryFreeIncidentFaceSelector.faceOf_selectedWitnessEdge_eq_of_mem_peelFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    {f : AmbientFace emb.faces} (hf : f ∈ selector.peelFaces) :
    ∃ he : selector.selectedWitnessEdge fallbackEdge f ∈
        interiorEdgeSupport emb.faceBoundary emb.faces,
      selector.faceOf (selector.selectedWitnessEdge fallbackEdge f) he = f := by
  classical
  rcases Finset.mem_image.1 hf with ⟨e, _heMem, hface⟩
  let h : ∃ e' : G.edgeSet,
      ∃ he' : e' ∈ interiorEdgeSupport emb.faceBoundary emb.faces,
        selector.faceOf e' he' = f := ⟨e.1, e.2, hface⟩
  rw [BoundaryFreeIncidentFaceSelector.selectedWitnessEdge, dif_pos h]
  exact Classical.choose_spec h

theorem boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_selectedWitnessEdge_eq
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    {f : AmbientFace emb.faces}
    (hf : f ∈
      (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data).peelFaces) :
    (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data).selectedWitnessEdge
        data.fallbackEdge f =
      rootedSharedInteriorEdgeOfPairwiseUnique
        emb.faceBoundary emb.faces data.hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          data.roots data.hcoverRoots data.hsepRoots)
        data.fallbackEdge f := by
  rcases
    (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data)
      |>.faceOf_selectedWitnessEdge_eq_of_mem_peelFaces data.fallbackEdge hf with
    ⟨heInterior, hface⟩
  have hroot :=
    rootedSharedInteriorEdge_boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_faceOf_eq
      data heInterior
  rw [hface] at hroot
  exact hroot.symm

theorem boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_strictDescent
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :
    ∀ f ∈
      (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data).peelFaces,
      ∀ e ∈ (emb.faceBoundary f.1).erase
        ((boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data).selectedWitnessEdge
          data.fallbackEdge f),
        e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
          ∃ g ∈
            (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data).peelFaces,
            (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data).selectedWitnessEdge
                data.fallbackEdge g = e ∧
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist f
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    data.roots data.hcoverRoots data.hsepRoots f) <
                (interiorDualSpanningForest emb.faceBoundary emb.faces).dist g
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    data.roots data.hcoverRoots data.hsepRoots g) := by
  classical
  let selector :=
    boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data
  intro f hf e he
  have hfData :
      f ∈ data.peelFaces :=
    boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_peelFaces_subset
      data hf
  have hselectedF :
      selector.selectedWitnessEdge data.fallbackEdge f =
        rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge f := by
    simpa [selector] using
      boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_selectedWitnessEdge_eq
        data hf
  have heEraseRoot :
      e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge f) := by
    simpa [selector, hselectedF] using he
  have heFace : e ∈ emb.faceBoundary f.1 := (Finset.mem_erase.1 he).2
  have hneSelected : e ≠ selector.selectedWitnessEdge data.fallbackEdge f :=
    (Finset.mem_erase.1 he).1
  rcases data.hchildren f hfData e heEraseRoot with hboundary | ⟨g, hgData, hgf, heg⟩
  · exact Or.inl (boundaryData.hambientBoundaryCover hboundary)
  · have hgfAdj :
        (interiorDualGraph emb.faceBoundary emb.faces).Adj g f :=
      interiorDualSpanningForest_le emb.faceBoundary emb.faces
        (parentTowardsRoot_some_adj
          (interiorDualSpanningForest emb.faceBoundary emb.faces)
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            data.roots data.hcoverRoots data.hsepRoots)
          hgf)
    have hgf_ne : g.1 ≠ f.1 :=
      (interiorDualGraph_adj_iff emb.faceBoundary emb.faces).1 hgfAdj |>.1
    have heInterior : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces := by
      exact (mem_interiorEdgeSupport_iff emb.faceBoundary emb.faces).2
        ⟨Finset.mem_biUnion.2 ⟨g.1, g.2, heg⟩,
          totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
            emb.faceBoundary emb.faces data.hall g.2 f.2 hgf_ne heg heFace⟩
    have hfaceMem :
        e ∈ emb.faceBoundary (selector.faceOf e heInterior).1 := by
      simpa [selector] using
        parentPeelFaceOfInteriorEdge_edge_mem_faceBoundary data heInterior
    have hrootFaceOf :=
      rootedSharedInteriorEdge_boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_faceOf_eq
        data heInterior
    have hfaceChoice_eq_g : selector.faceOf e heInterior = g := by
      rcases
        eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
          emb.faceBoundary emb.faces data.hall g.2 f.2
          (selector.faceOf e heInterior).2 hgf_ne heg heFace hfaceMem with
        hval | hval
      · exact Subtype.ext hval
      · have hfaceChoice_eq_f : selector.faceOf e heInterior = f :=
          Subtype.ext hval
        have hrootF :
            rootedSharedInteriorEdgeOfPairwiseUnique
              emb.faceBoundary emb.faces data.hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                data.roots data.hcoverRoots data.hsepRoots)
              data.fallbackEdge f = e := by
          simpa [selector, hfaceChoice_eq_f] using hrootFaceOf
        have hselected_eq_e : selector.selectedWitnessEdge data.fallbackEdge f = e :=
          hselectedF.trans hrootF
        exact False.elim (hneSelected hselected_eq_e.symm)
    have hgSelector :
        g ∈ selector.peelFaces := by
      rw [← hfaceChoice_eq_g]
      exact selector.faceOf_mem_peelFaces heInterior
    have hselectedG : selector.selectedWitnessEdge data.fallbackEdge g = e := by
      rw [← hfaceChoice_eq_g]
      exact
        selector.selectedWitnessEdge_eq_of_faceOf data.fallbackEdge
          (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_injective
            data)
          heInterior
    have hgfRootData :
        (data.toInteriorDualRootDistanceParentPeelData).parentFace g = some f := by
      simpa [InteriorDualBoundaryRootParentPeelData.toInteriorDualRootDistanceParentPeelData]
        using hgf
    have hlt :=
      (data.toInteriorDualRootDistanceParentPeelData).hdist hgfRootData
    refine Or.inr ⟨g, by simpa [selector] using hgSelector, by simpa [selector] using hselectedG, ?_⟩
    simpa [InteriorDualBoundaryRootParentPeelData.toInteriorDualRootDistanceParentPeelData]
      using hlt

theorem BoundaryFreeIncidentFaceSelector.selectedWitnessEdge_injective_on_peelFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    {f g : AmbientFace emb.faces} (hf : f ∈ selector.peelFaces)
    (hg : g ∈ selector.peelFaces)
    (hfg : selector.selectedWitnessEdge fallbackEdge f =
      selector.selectedWitnessEdge fallbackEdge g) :
    f = g := by
  rcases selector.faceOf_selectedWitnessEdge_eq_of_mem_peelFaces fallbackEdge hf with
    ⟨hef, hfacef⟩
  rcases selector.faceOf_selectedWitnessEdge_eq_of_mem_peelFaces fallbackEdge hg with
    ⟨heg, hfaceg⟩
  let hef' : selector.selectedWitnessEdge fallbackEdge g ∈
      interiorEdgeSupport emb.faceBoundary emb.faces := by
    simpa [hfg] using hef
  have hfacef' :
      selector.faceOf (selector.selectedWitnessEdge fallbackEdge g) hef' = f := by
    simpa [hfg, hef'] using hfacef
  have hsame :
      selector.faceOf (selector.selectedWitnessEdge fallbackEdge g) hef' =
        selector.faceOf (selector.selectedWitnessEdge fallbackEdge g) heg := by
    congr
  exact hfacef'.symm.trans (hsame.trans hfaceg)

/-- The selected-face dependency relation induced by the selector strict-descent condition.  A
dependency `f → g` means that the selected witness of `g` occurs as a non-witness remainder edge on
`f` and is not part of either ambient annulus boundary. -/
def BoundaryFreeIncidentFaceSelector.remainderDependency {G : SimpleGraph V}
    {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (f g : AmbientFace emb.faces) : Prop :=
  f ∈ selector.peelFaces ∧
    g ∈ selector.peelFaces ∧
      selector.selectedWitnessEdge fallbackEdge g ∈
          (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f) ∧
        selector.selectedWitnessEdge fallbackEdge g ∉
          boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary

theorem BoundaryFreeIncidentFaceSelector.faceDistance_lt_of_remainderDependency
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    {f g : AmbientFace emb.faces}
    (hdep : selector.remainderDependency boundaryData fallbackEdge f g) :
    faceDistance f < faceDistance g := by
  rcases hdep with ⟨hf, hg, hmem, hnotBoundary⟩
  rcases hrest f hf (selector.selectedWitnessEdge fallbackEdge g) hmem with
    hboundary | ⟨u, hu, hwu, hlt⟩
  · exact (hnotBoundary hboundary).elim
  · have hug : u = g :=
      selector.selectedWitnessEdge_injective_on_peelFaces fallbackEdge hu hg hwu
    simpa [hug] using hlt

/-- The strict-distance selector condition rules out any nonempty finite cycle of selected-face
remainder dependencies.  This is the selector-level version of the witness-cover cycle obstruction:
closed dependency chains must be broken by the ambient boundary split before the selector can lower
to an annulus construction. -/
theorem BoundaryFreeIncidentFaceSelector.false_of_remainderDependency_cycle
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    {cycle : List (AmbientFace emb.faces)}
    (hne : cycle ≠ [])
    (hchain : List.IsChain (selector.remainderDependency boundaryData fallbackEdge) cycle)
    (hloop : selector.remainderDependency boundaryData fallbackEdge
      (cycle.getLast hne) (cycle.head hne)) :
    False := by
  have hheightChain :
      List.IsChain (fun f g => faceDistance f < faceDistance g) cycle := by
    exact hchain.imp (by
      intro f g hdep
      exact selector.faceDistance_lt_of_remainderDependency boundaryData fallbackEdge
        faceDistance hrest hdep)
  have hloopHeight : faceDistance (cycle.getLast hne) < faceDistance (cycle.head hne) :=
    selector.faceDistance_lt_of_remainderDependency boundaryData fallbackEdge
      faceDistance hrest hloop
  exact false_of_isChain_height_lt_and_getLast_lt_head faceDistance hne hheightChain hloopHeight

/-- A finite selected-face set cannot be closed under selector remainder dependencies when those
dependencies satisfy the strict-distance side condition.  Thus any nonempty selector satisfying
`hrest` must expose at least one selected face whose non-boundary remainders are not all consumed
by selected witnesses. -/
theorem BoundaryFreeIncidentFaceSelector.false_of_total_remainderDependency
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hne : selector.peelFaces.Nonempty)
    (htotal : ∀ f ∈ selector.peelFaces,
      ∃ g, selector.remainderDependency boundaryData fallbackEdge f g) :
    False := by
  classical
  let heights := selector.peelFaces.image faceDistance
  have hheights : heights.Nonempty := hne.image faceDistance
  rcases Finset.mem_image.1 (Finset.max'_mem heights hheights) with
    ⟨f, hf, hfmax⟩
  rcases htotal f hf with ⟨g, hdep⟩
  have hg : g ∈ selector.peelFaces := hdep.2.1
  have hlt : faceDistance f < faceDistance g :=
    selector.faceDistance_lt_of_remainderDependency boundaryData fallbackEdge faceDistance
      hrest hdep
  have hgmax : faceDistance g ≤ heights.max' hheights :=
    Finset.le_max' heights (faceDistance g) (Finset.mem_image.2 ⟨g, hg, rfl⟩)
  exact (not_lt_of_ge (by simpa [hfmax] using hgmax) hlt).elim

/-- Constructive-facing form of `false_of_total_remainderDependency`: every nonempty
strict-descent selector has a selected face with no outgoing remainder dependency.  This is the
face at which a source-to-selector construction must expose an ambient-boundary break rather than
another selected witness. -/
theorem BoundaryFreeIncidentFaceSelector.exists_face_without_remainderDependency
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hne : selector.peelFaces.Nonempty) :
    ∃ f ∈ selector.peelFaces,
      ∀ g, ¬ selector.remainderDependency boundaryData fallbackEdge f g := by
  classical
  by_contra hnone
  have htotal : ∀ f ∈ selector.peelFaces,
      ∃ g, selector.remainderDependency boundaryData fallbackEdge f g := by
    intro f hf
    by_contra hmissing
    exact hnone ⟨f, hf, by
      intro g hdep
      exact hmissing ⟨g, hdep⟩⟩
  exact selector.false_of_total_remainderDependency boundaryData fallbackEdge faceDistance
    hrest hne htotal

/-- For a selected face in a strict-descent selector, having no outgoing selector dependency is
equivalent to the local boundary-break condition that every non-witness remainder edge is on the
ambient annulus boundary split. -/
theorem BoundaryFreeIncidentFaceSelector.no_remainderDependency_iff_boundary_remainders
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    {f : AmbientFace emb.faces} (hf : f ∈ selector.peelFaces) :
    (∀ g : AmbientFace emb.faces,
        ¬ selector.remainderDependency boundaryData fallbackEdge f g) ↔
      ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
        e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary := by
  constructor
  · intro hterminal e he
    rcases hrest f hf e he with hboundary | ⟨g, hg, hge, _hlt⟩
    · exact hboundary
    · by_contra hnotBoundary
      exact
        (hterminal g
          ⟨hf, hg, by simpa [hge] using he, by simpa [hge] using hnotBoundary⟩).elim
  · intro hboundary g hdep
    exact hdep.2.2.2
      (hboundary (selector.selectedWitnessEdge fallbackEdge g) hdep.2.2.1)

/-- Boundary-break form of the terminal selector face.  In any nonempty strict-descent selector,
some selected face has all non-witness remainder edges on the ambient annulus boundary. -/
theorem BoundaryFreeIncidentFaceSelector.exists_terminal_face_boundary_remainders
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hne : selector.peelFaces.Nonempty) :
    ∃ f ∈ selector.peelFaces,
      ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
        e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary := by
  rcases selector.exists_face_without_remainderDependency boundaryData fallbackEdge faceDistance
      hrest hne with
    ⟨f, hf, hterminal⟩
  exact ⟨f, hf,
    (selector.no_remainderDependency_iff_boundary_remainders boundaryData fallbackEdge
      faceDistance hrest hf).1 hterminal⟩

theorem BoundaryFreeIncidentFaceSelector.exists_terminal_face_boundary_remainders_of_mem_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ∃ f ∈ selector.peelFaces,
      ∀ e' ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
        e' ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary := by
  exact selector.exists_terminal_face_boundary_remainders boundaryData fallbackEdge
    faceDistance hrest (selector.peelFaces_nonempty_of_mem_interiorEdgeSupport he)

theorem BoundaryFreeIncidentFaceSelector.exists_terminal_face_boundary_remainders_of_interiorEdgeSupport_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    ∃ f ∈ selector.peelFaces,
      ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
        e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary := by
  exact selector.exists_terminal_face_boundary_remainders boundaryData fallbackEdge
    faceDistance hrest
    (selector.peelFaces_nonempty_of_interiorEdgeSupport_nonempty hInterior)

theorem
    BoundaryFreeIncidentFaceSelector.faceBoundary_disjoint_selectedBoundarySupport_of_mem_peelFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb)
    {f : AmbientFace emb.faces} (hf : f ∈ selector.peelFaces) :
    Disjoint (emb.faceBoundary f.1)
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
  rcases Finset.mem_image.1 hf with ⟨e, _heMem, hface⟩
  have hdisjoint :=
    selector.faceOf_disjoint_selectedBoundarySupport (e := e.1) e.2
  simpa [hface] using hdisjoint

/-- Selector-to-construction bridge. A boundary-free selector becomes the weak annulus
construction shell once its selected faces are injective over interior edges and every
non-witness remainder edge is either ambient-boundary support or the selected witness of a
strictly deeper selected face. -/
noncomputable def BoundaryFreeIncidentFaceSelector.toPlanarBoundaryAnnulusConstruction
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g) :
    PlanarBoundaryAnnulusConstruction emb := by
  refine
    { toPlanarBoundaryAnnulusBoundaryData := boundaryData
      peelFaces := selector.peelFaces
      witnessEdge := selector.selectedWitnessEdge fallbackEdge
      faceDistance := faceDistance
      hcover := ?_
      hwitness := ?_
      hrest := ?_ }
  · intro e heInterior
    exact
      Finset.mem_image.2
        ⟨selector.faceOf e heInterior,
          selector.faceOf_mem_peelFaces heInterior,
          selector.selectedWitnessEdge_eq_of_faceOf fallbackEdge hinjective heInterior⟩
  · intro f hf
    exact selector.selectedWitnessEdge_mem_faceBoundary_of_mem_peelFaces fallbackEdge hf
  · intro f hf e he
    exact hrest f hf e he

/-- The selector dependency relation is exactly the construction dependency relation after
lowering a strict-descent selector to a `PlanarBoundaryAnnulusConstruction`.  The construction
relation includes the strict face-distance inequality as a field; on the selector side that
inequality is recovered from the selector `hrest` hypothesis. -/
theorem BoundaryFreeIncidentFaceSelector.toPlanarBoundaryAnnulusConstruction_remainderDependency_iff
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    {f g : AmbientFace emb.faces} :
    (selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge faceDistance
        hinjective hrest).remainderDependency f g ↔
      selector.remainderDependency boundaryData fallbackEdge f g := by
  dsimp [PlanarBoundaryAnnulusConstruction.remainderDependency,
    BoundaryFreeIncidentFaceSelector.remainderDependency,
    BoundaryFreeIncidentFaceSelector.toPlanarBoundaryAnnulusConstruction]
  constructor
  · intro hdep
    exact ⟨hdep.1, hdep.2.1, hdep.2.2.1, hdep.2.2.2.1⟩
  · intro hdep
    refine ⟨hdep.1, hdep.2.1, hdep.2.2.1, hdep.2.2.2, ?_⟩
    exact selector.faceDistance_lt_of_remainderDependency boundaryData fallbackEdge
      faceDistance hrest hdep

/-- Lowering a strict-descent selector to an annulus construction preserves the terminal
no-dependency condition exactly. -/
theorem BoundaryFreeIncidentFaceSelector.toPlanarBoundaryAnnulusConstruction_no_remainderDependency_iff
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    {f : AmbientFace emb.faces} :
    (∀ g : AmbientFace emb.faces,
        ¬ (selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge faceDistance
          hinjective hrest).remainderDependency f g) ↔
      ∀ g : AmbientFace emb.faces,
        ¬ selector.remainderDependency boundaryData fallbackEdge f g := by
  constructor
  · intro hterminal g hdep
    exact hterminal g
      ((selector.toPlanarBoundaryAnnulusConstruction_remainderDependency_iff boundaryData
        fallbackEdge faceDistance hinjective hrest).2 hdep)
  · intro hterminal g hdep
    exact hterminal g
      ((selector.toPlanarBoundaryAnnulusConstruction_remainderDependency_iff boundaryData
        fallbackEdge faceDistance hinjective hrest).1 hdep)

/-- The construction obtained from a boundary-free selector has selected-boundary-free peeled
faces. The stronger `PlanarBoundaryAnnulusConstructionBoundarySupportFaceData` shell still
requires separate non-peeled-face and current-frontier hypotheses; this lemma records the part
supplied directly by the selector. -/
theorem BoundaryFreeIncidentFaceSelector.toPlanarBoundaryAnnulusConstruction_hpeelInterior
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g) :
    ∀ f ∈ (selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge faceDistance
        hinjective hrest).peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
  intro f hf
  exact selector.faceBoundary_disjoint_selectedBoundarySupport_of_mem_peelFaces hf

/-- Same-embedding annulus construction induced by the canonical parent selector. This packages
the selector witness map, the root-distance measure, and the strict-descent proof into the
construction surface used by the downstream annulus shells. -/
noncomputable def planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryAnnulusConstruction emb :=
  let selector :=
    boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data
  selector.toPlanarBoundaryAnnulusConstruction
    boundaryData
    data.fallbackEdge
    (fun f =>
      (interiorDualSpanningForest emb.faceBoundary emb.faces).dist f
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          data.roots data.hcoverRoots data.hsepRoots f))
    (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_injective data)
    (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_strictDescent
      boundaryData data)

/-- Annulus-side specialization of the selector-driven construction. -/
noncomputable def planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb) :
    PlanarBoundaryAnnulusConstruction emb :=
  planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
    data.boundaryData data.interiorData

/-- The selector construction induced by exact boundary-root parent data is already
construction-side parent-oriented on the same embedding. Each selected witness edge is the
canonical rooted shared interior edge, so it also lies on the unique parent face toward the
separated covering root set, and the stored face distance is exactly the interior-dual root
distance. -/
theorem parentWitnessOrientation_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :
    (planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
      boundaryData data).ParentWitnessOrientation := by
  let T := interiorDualSpanningForest emb.faceBoundary emb.faces
  let rootFace : AmbientFace emb.faces → AmbientFace emb.faces :=
    interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
      data.hcoverRoots data.hsepRoots
  have hdisj : Disjoint data.peelFaces data.roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      emb.faceBoundary emb.faces data.peelFaces data.roots
      data.hpeelInterior data.hrootsBoundary
  intro g hg
  have hgData : g ∈ data.peelFaces :=
    boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_peelFaces_subset
      data hg
  have hgroot : g ≠ rootFace g :=
    ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
      emb.faceBoundary emb.faces data.peelFaces data.roots
      data.hcoverRoots data.hsepRoots hdisj hgData
  have hgreach := reachable_interiorDualSpanningForestRoot
    emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots g
  rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := g)
      hgreach hgroot with ⟨p, hgp, hadjgp, hdistgp⟩
  refine ⟨p, ?_, ?_⟩
  · rw [show
        (planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
          boundaryData data).witnessEdge g =
          rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
            rootFace data.fallbackEdge g by
        simpa [planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootParentPeelData,
          rootFace] using
          boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_selectedWitnessEdge_eq
            data hg]
    exact
      rootedSharedInteriorEdgeOfPairwiseUnique_mem_parent_faceBoundary
        emb.faceBoundary emb.faces data.hunique rootFace data.fallbackEdge hgp
  · have hroot : rootFace p = rootFace g := by
      simpa [rootFace] using
        (interiorDualSpanningForestRoot_eq_of_adj
          emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots hadjgp).symm
    change T.dist p (rootFace p) < T.dist g (rootFace g)
    rw [hroot]
    omega

/-- Annulus-root specialization of the same exact parent-witness orientation theorem. -/
theorem parentWitnessOrientation_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb) :
    (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
      data).ParentWitnessOrientation := by
  simpa [planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData] using
    parentWitnessOrientation_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
      data.boundaryData data.interiorData

/-- The exact selector-driven boundary-root parent construction cannot coincide with the stronger
selected-boundary-support annulus shell on the same embedding. That shell still forces the
zero-stratum positive-frontier bookkeeping that strict parent orientation forbids. -/
theorem
    not_exists_planarBoundaryAnnulusConstructionBoundarySupportFaceData_with_planarBoundaryAnnulusRootParentPeelConstruction
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb) :
    ¬ ∃ supportData : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb,
      supportData.construction =
        planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData data := by
  have horient :
      (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
        data).ParentWitnessOrientation :=
    parentWitnessOrientation_of_planarBoundaryAnnulusRootParentPeelData data
  rintro ⟨supportData, hconstruction⟩
  have hnot :
      ¬ (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
        data).ParentWitnessOrientation := by
    simpa [hconstruction] using supportData.not_parentWitnessOrientation
  exact hnot horient

/-- The only non-peeled faces not already handled by the boundary-root parent package are peeled
faces missed by the selector image. A precise selector-deficit selected-boundary hypothesis closes
exactly that gap. -/
theorem
    nonPeelSelectedBoundary_of_boundaryData_and_interiorDualBoundaryRootParentPeelData_and_selectorDeficitSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ data.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
              boundaryData data).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
            boundaryData data).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  intro f hf
  by_cases hfData : f ∈ data.peelFaces
  · exact hselectorDeficitSelectedBoundary f hfData hf
  · exact data.exists_mem_selectedBoundarySupport_of_not_mem_peelFaces hfData

/-- Annulus-root specialization of the same selector-deficit repair. -/
theorem
    nonPeelSelectedBoundary_of_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ data.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              data).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
            data).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  intro f hf
  by_cases hfData : f ∈ data.interiorData.peelFaces
  · exact hselectorDeficitSelectedBoundary f hfData hf
  · exact data.interiorData.exists_mem_selectedBoundarySupport_of_not_mem_peelFaces hfData

/-- The repaired selector-deficit premise is strictly local: any stronger hypothesis saying that
every non-peeled construction face already touches selected-boundary support implies it
immediately by restriction to selector-deficit peeled faces. -/
theorem
    selectorDeficitSelectedBoundary_of_planarBoundaryAnnulusRootParentPeelData_and_nonPeelSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
            data).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :
    ∀ f : AmbientFace emb.faces,
      f ∈ data.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              data).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  intro f _ hf
  exact hnonPeelSelectedBoundary f hf

/-- Selector-to-boundary-support-face-data bridge. The selector supplies the peeled-face
selected-boundary avoidance and the construction cover; the genuinely additional annulus
requirements are kept as explicit hypotheses: non-peeled faces touch selected-boundary support,
outer and inner ambient boundary faces are separated, and the positive current outer frontiers are
nonempty and pairwise disjoint. -/
noncomputable def BoundaryFreeIncidentFaceSelector.toPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉ selector.peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
      ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ boundaryData.outerAmbientBoundary) ∧
          (∃ e ∈ emb.faceBoundary f.1, e ∈ boundaryData.innerAmbientBoundary)))
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge
              faceDistance hinjective hrest).numCollars,
        0 < i.1 →
          ((selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge
            faceDistance hinjective hrest).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge
              faceDistance hinjective hrest).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge
              faceDistance hinjective hrest).currentOuterBoundary i)
            ((selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge
              faceDistance hinjective hrest).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb := by
  let construction :=
    selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge faceDistance
      hinjective hrest
  refine
    { construction := construction
      hpeelInterior := ?_
      hnonPeelSelectedBoundary := ?_
      hboundaryFaceDisjoint := ?_
      hcurrentOuterBoundaryNonempty := ?_
      hcurrentOuterBoundaryDisjoint := ?_ }
  · intro f hf
    simpa [construction] using
      selector.toPlanarBoundaryAnnulusConstruction_hpeelInterior boundaryData fallbackEdge
        faceDistance hinjective hrest f hf
  · intro f hf
    simpa [construction] using hnonPeelSelectedBoundary f hf
  · have hseparated : ∀ f : AmbientFace emb.faces,
        ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ construction.outerAmbientBoundary) ∧
            (∃ e ∈ emb.faceBoundary f.1, e ∈ construction.innerAmbientBoundary)) := by
      intro f
      simpa [construction] using hboundaryFaceSeparated f
    exact construction.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryFaceSeparated
      hseparated
  · intro i hi
    simpa [construction] using hcurrentOuterBoundaryNonempty i hi
  · intro i j hi hj hij
    simpa [construction] using hcurrentOuterBoundaryDisjoint (i := i) (j := j) hi hj hij

/-- Same-embedding lowering from the honest closed-walk face-boundary geometry plus annulus-root
canonical parent data to the selected-boundary-contact construction shell. The exact additional
burden is isolated to peeled faces that the selector never chooses: those faces must themselves
touch selected-boundary support. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb := by
  let selector :=
    boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusRootParentPeelData parentData
  unfold planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
    planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootParentPeelData at hselectorDeficitSelectedBoundary hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint
  have hnonPeelSelectedBoundary :
      ∀ f : AmbientFace emb.faces,
        f ∉ selector.peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
    intro f hf
    by_cases hfData : f ∈ parentData.interiorData.peelFaces
    · exact hselectorDeficitSelectedBoundary f hfData hf
    · exact
        parentData.interiorData.exists_mem_selectedBoundarySupport_of_not_mem_peelFaces hfData
  exact
    selector.toPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
      parentData.boundaryData
      parentData.interiorData.fallbackEdge
      (fun f =>
        (interiorDualSpanningForest emb.faceBoundary emb.faces).dist f
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            parentData.interiorData.roots parentData.interiorData.hcoverRoots
            parentData.interiorData.hsepRoots f))
      (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_injective
        parentData.interiorData)
      (by
        simpa [selector, boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusRootParentPeelData]
          using
            boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_strictDescent
              parentData.boundaryData parentData.interiorData)
      hnonPeelSelectedBoundary
      (by
        intro f
        simpa [hparentBoundary] using
          boundaryData.boundaryFaceSeparated_of_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
            boundaryGeom hboundaryArc (f := f))
      hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint

/-- Successor-cycle form of the same construction-shell lowering. This matches the exact
boundary-order interface currently used in the repaired v23/v23.5 route. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
    boundaryData dartCycles.toPlanarBoundaryClosedWalkEmbeddingData hboundaryArc
    parentData hparentBoundary hselectorDeficitSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- Core construction-layer inconsistency behind the repaired exact-shell obstruction.  Once
closed-walk annulus boundary data already lowers same-embedding parent-peel data to the
selected-boundary-support construction shell, the selector-deficit selected-boundary premise and
the positive current-outer-boundary conditions force a contradiction with parent-witness
orientation on that same construction. -/
theorem
    false_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    False := by
  exact
    (not_exists_planarBoundaryAnnulusConstructionBoundarySupportFaceData_with_planarBoundaryAnnulusRootParentPeelConstruction
      parentData) ⟨
        planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
          boundaryData boundaryGeom hboundaryArc parentData hparentBoundary
          hselectorDeficitSelectedBoundary hcurrentOuterBoundaryNonempty
          hcurrentOuterBoundaryDisjoint,
        rfl⟩

/-- Successor-cycle form of the same core construction-layer inconsistency.  The repaired
boundary-order shell assumptions are only used to manufacture the selected-boundary-support
construction data; the contradiction itself is purely construction-side. -/
theorem
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (parentData : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hparentBoundary :
      parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData)
    (hselectorDeficitSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∈ parentData.interiorData.peelFaces →
        f ∉
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).peelFaces →
          ∃ e ∈ emb.faceBoundary f.1,
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
              parentData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary j)) :
    False := by
  exact
    (not_exists_planarBoundaryAnnulusConstructionBoundarySupportFaceData_with_planarBoundaryAnnulusRootParentPeelConstruction
      parentData) ⟨
        planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary
          boundaryData dartCycles hboundaryArc parentData hparentBoundary
          hselectorDeficitSelectedBoundary hcurrentOuterBoundaryNonempty
          hcurrentOuterBoundaryDisjoint,
        rfl⟩

/-- Fixed-embedding nonexistence form of the same closed-walk boundary-order contradiction. -/
theorem
    not_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    ¬ ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
        (∀ f : AmbientFace emb.faces,
          f ∈ parentData.interiorData.peelFaces →
            f ∉
                (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).peelFaces →
              ∃ e ∈ emb.faceBoundary f.1,
                e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary j)) := by
  rintro ⟨parentData, hparentBoundary, hselectorDeficitSelectedBoundary,
    hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    false_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
      boundaryData boundaryGeom hboundaryArc parentData hparentBoundary
      hselectorDeficitSelectedBoundary hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint

/-- Fixed-embedding nonexistence form of the same successor-cycle boundary-order contradiction. -/
theorem
    not_exists_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    ¬ ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
        (∀ f : AmbientFace emb.faces,
          f ∈ parentData.interiorData.peelFaces →
            f ∉
                (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).peelFaces →
              ∃ e ∈ emb.faceBoundary f.1,
                e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary j)) := by
  rintro ⟨parentData, hparentBoundary, hselectorDeficitSelectedBoundary,
    hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
      boundaryData dartCycles hboundaryArc parentData hparentBoundary
      hselectorDeficitSelectedBoundary hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint

/-- Graph-level form of the same construction-side contradiction on the closed-walk
boundary-order shell.  No embedding can simultaneously realize boundary reachability, closed-walk
boundary geometry with selected-boundary arcs, same-split annulus-root parent-peel data, the
selector-deficit selected-boundary contact premise, and the older positive
`currentOuterBoundary` side conditions. -/
theorem
    not_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb,
      ∃ _hboundaryArc : ∀ f : AmbientFace emb.faces,
        (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
        (∀ f : AmbientFace emb.faces,
          f ∈ parentData.interiorData.peelFaces →
            f ∉
                (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).peelFaces →
              ∃ e ∈ emb.faceBoundary f.1,
                e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary j)) := by
  rintro ⟨emb, boundaryData, boundaryGeom, hboundaryArc, parentData, hparentBoundary,
    hselectorDeficitSelectedBoundary, hcurrentOuterBoundaryNonempty,
    hcurrentOuterBoundaryDisjoint⟩
  exact
    false_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
      boundaryData boundaryGeom hboundaryArc parentData hparentBoundary
      hselectorDeficitSelectedBoundary hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint

/-- Graph-level form of the same construction-side contradiction on the live successor-cycle
boundary-order shell.  So the repaired parent-peel plus selector-deficit plus positive
`currentOuterBoundary` package is globally impossible already at the raw boundary-order layer,
before adding any exact one-collar or exact-v23 residual hypotheses. -/
theorem
    not_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ _hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ parentData : PlanarBoundaryAnnulusRootParentPeelData emb,
        parentData.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
        (∀ f : AmbientFace emb.faces,
          f ∈ parentData.interiorData.peelFaces →
            f ∉
                (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).peelFaces →
              ∃ e ∈ emb.faceBoundary f.1,
                e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                parentData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_planarBoundaryAnnulusRootParentPeelData
                  parentData).currentOuterBoundary j)) := by
  rintro ⟨emb, boundaryData, dartCycles, hboundaryArc, parentData, hparentBoundary,
    hselectorDeficitSelectedBoundary, hcurrentOuterBoundaryNonempty,
    hcurrentOuterBoundaryDisjoint⟩
  exact
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_planarBoundaryAnnulusRootParentPeelData_and_selectorDeficitSelectedBoundary_and_currentOuterBoundary
      boundaryData dartCycles hboundaryArc parentData hparentBoundary
      hselectorDeficitSelectedBoundary hcurrentOuterBoundaryNonempty
      hcurrentOuterBoundaryDisjoint

/-- Any selector satisfying the full annulus boundary-support side conditions excludes a forcing
interior edge on the same embedding. This packages the selector construction with the existing
forcing-edge obstruction rather than routing through algebraic synthesis. -/
theorem BoundaryFreeIncidentFaceSelector.not_nonempty_forcingInteriorEdgeWitness_of_boundarySupportFaceData_conditions
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (selector : BoundaryFreeIncidentFaceSelector emb)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (faceDistance : AmbientFace emb.faces → ℕ)
    (hinjective :
      ∀ {e₁ e₂ : G.edgeSet}
        (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
        (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
          selector.faceOf e₁ he₁ = selector.faceOf e₂ he₂ → e₁ = e₂)
    (hrest :
      ∀ f ∈ selector.peelFaces,
        ∀ e ∈ (emb.faceBoundary f.1).erase (selector.selectedWitnessEdge fallbackEdge f),
          e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary ∨
            ∃ g ∈ selector.peelFaces,
              selector.selectedWitnessEdge fallbackEdge g = e ∧
                faceDistance f < faceDistance g)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉ selector.peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hboundaryFaceSeparated : ∀ f : AmbientFace emb.faces,
      ¬ ((∃ e ∈ emb.faceBoundary f.1, e ∈ boundaryData.outerAmbientBoundary) ∧
          (∃ e ∈ emb.faceBoundary f.1, e ∈ boundaryData.innerAmbientBoundary)))
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge
              faceDistance hinjective hrest).numCollars,
        0 < i.1 →
          ((selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge
            faceDistance hinjective hrest).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge
              faceDistance hinjective hrest).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge
              faceDistance hinjective hrest).currentOuterBoundary i)
            ((selector.toPlanarBoundaryAnnulusConstruction boundaryData fallbackEdge
              faceDistance hinjective hrest).currentOuterBoundary j)) :
    ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_nonempty_forcingInteriorEdgeWitness_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      (selector.toPlanarBoundaryAnnulusConstructionBoundarySupportFaceData boundaryData fallbackEdge
        faceDistance hinjective hrest hnonPeelSelectedBoundary hboundaryFaceSeparated
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint)

end Theorem49ForcingInteriorEdgeObstruction

end Mettapedia.GraphTheory.FourColor
