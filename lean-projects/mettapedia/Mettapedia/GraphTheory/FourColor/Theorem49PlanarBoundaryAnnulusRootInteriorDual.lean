import Mettapedia.GraphTheory.FourColor.PlanarBoundaryClosedWalkSource
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryOuterBoundaryRootInteriorDual

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Annulus-side version of the boundary-root adjacency-distance package where roots are allowed
to meet either distinguished ambient boundary component. This is the constructive two-sided
replacement for the outer-boundary-only root localization: it records compatibility with the
annulus boundary split without forcing all root faces onto the same component. -/
structure PlanarBoundaryAnnulusRootAdjDistancePeelData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  boundaryData : PlanarBoundaryAnnulusBoundaryData emb
  interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary
  hrootsBoundary : ∀ r ∈ interiorData.roots,
    ∃ e ∈ emb.faceBoundary r.1,
      e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary

/-- Annulus-side version of the canonical parent package where roots are allowed to meet either
distinguished ambient boundary component. -/
structure PlanarBoundaryAnnulusRootParentPeelData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  boundaryData : PlanarBoundaryAnnulusBoundaryData emb
  interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary
  hrootsBoundary : ∀ r ∈ interiorData.roots,
    ∃ e ∈ emb.faceBoundary r.1,
      e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary

/-- Graph-level existence form of the two-sided annulus-root adjacency-distance target. -/
def AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb)

/-- Graph-level existence form of the two-sided annulus-root canonical parent target. -/
def AdmitsPlanarBoundaryAnnulusRootParentPeelData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb)

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_of_mem_roots
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.interiorData.roots) :
    f ∈ data.boundaryData.outerBoundaryFaces ∪ data.boundaryData.innerBoundaryFaces := by
  rcases data.hrootsBoundary f hf with ⟨e, hef, heBoundary⟩
  exact (data.boundaryData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_iff).2
    ⟨e, hef, by
      rcases Finset.mem_union.1 heBoundary with heOuter | heInner
      · exact data.boundaryData.houterAmbientBoundarySubset heOuter
      · exact data.boundaryData.hinnerAmbientBoundarySubset heInner⟩

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.roots_subset_boundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb) :
    data.interiorData.roots ⊆
      data.boundaryData.outerBoundaryFaces ∪ data.boundaryData.innerBoundaryFaces := by
  intro f hf
  exact data.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_of_mem_roots hf

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.exists_mem_selectedBoundarySupport_of_mem_roots
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.interiorData.roots) :
    ∃ e ∈ emb.faceBoundary f.1,
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  rcases data.hrootsBoundary f hf with ⟨e, hef, heBoundary⟩
  refine ⟨e, hef, ?_⟩
  rcases Finset.mem_union.1 heBoundary with heOuter | heInner
  · exact data.boundaryData.houterAmbientBoundarySubset heOuter
  · exact data.boundaryData.hinnerAmbientBoundarySubset heInner

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_of_not_mem_peelFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∉ data.interiorData.peelFaces) :
    f ∈ data.boundaryData.outerBoundaryFaces ∪ data.boundaryData.innerBoundaryFaces := by
  exact data.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_of_mem_roots
    (data.interiorData.mem_roots_of_not_mem_peelFaces hf)

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.exists_mem_selectedBoundarySupport_of_not_mem_peelFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∉ data.interiorData.peelFaces) :
    ∃ e ∈ emb.faceBoundary f.1,
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  exact data.exists_mem_selectedBoundarySupport_of_mem_roots
    (data.interiorData.mem_roots_of_not_mem_peelFaces hf)

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.not_mem_peelFaces_of_mem_outerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.boundaryData.outerBoundaryFaces) :
    f ∉ data.interiorData.peelFaces := by
  intro hfPeel
  rcases (data.boundaryData.mem_outerBoundaryFaces_iff).1 hf with ⟨e, hef, heOuter⟩
  exact (Finset.disjoint_left.mp (data.interiorData.hpeelInterior f hfPeel))
    hef (data.boundaryData.houterAmbientBoundarySubset heOuter)

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.not_mem_peelFaces_of_mem_innerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.boundaryData.innerBoundaryFaces) :
    f ∉ data.interiorData.peelFaces := by
  intro hfPeel
  rcases (data.boundaryData.mem_innerBoundaryFaces_iff).1 hf with ⟨e, hef, heInner⟩
  exact (Finset.disjoint_left.mp (data.interiorData.hpeelInterior f hfPeel))
    hef (data.boundaryData.hinnerAmbientBoundarySubset heInner)

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.mem_roots_of_mem_outerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.boundaryData.outerBoundaryFaces) :
    f ∈ data.interiorData.roots := by
  exact data.interiorData.mem_roots_of_not_mem_peelFaces
    (data.not_mem_peelFaces_of_mem_outerBoundaryFaces hf)

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.mem_roots_of_mem_innerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.boundaryData.innerBoundaryFaces) :
    f ∈ data.interiorData.roots := by
  exact data.interiorData.mem_roots_of_not_mem_peelFaces
    (data.not_mem_peelFaces_of_mem_innerBoundaryFaces hf)

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.outerBoundaryFaces_subset_roots
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb) :
    data.boundaryData.outerBoundaryFaces ⊆ data.interiorData.roots := by
  intro f hf
  exact data.mem_roots_of_mem_outerBoundaryFaces hf

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.innerBoundaryFaces_subset_roots
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb) :
    data.boundaryData.innerBoundaryFaces ⊆ data.interiorData.roots := by
  intro f hf
  exact data.mem_roots_of_mem_innerBoundaryFaces hf

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.exists_root_mem_outerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb) :
    ∃ f : AmbientFace emb.faces,
      f ∈ data.boundaryData.outerBoundaryFaces ∧
      f ∈ data.interiorData.roots := by
  rcases data.boundaryData.outerBoundaryFaces_nonempty with ⟨f, hfOuter⟩
  exact ⟨f, hfOuter, data.mem_roots_of_mem_outerBoundaryFaces hfOuter⟩

theorem PlanarBoundaryAnnulusRootAdjDistancePeelData.exists_root_mem_innerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb) :
    ∃ f : AmbientFace emb.faces,
      f ∈ data.boundaryData.innerBoundaryFaces ∧
      f ∈ data.interiorData.roots := by
  rcases data.boundaryData.innerBoundaryFaces_nonempty with ⟨f, hfInner⟩
  exact ⟨f, hfInner, data.mem_roots_of_mem_innerBoundaryFaces hfInner⟩

theorem PlanarBoundaryAnnulusRootParentPeelData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_of_mem_roots
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.interiorData.roots) :
    f ∈ data.boundaryData.outerBoundaryFaces ∪ data.boundaryData.innerBoundaryFaces := by
  rcases data.hrootsBoundary f hf with ⟨e, hef, heBoundary⟩
  exact (data.boundaryData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_iff).2
    ⟨e, hef, by
      rcases Finset.mem_union.1 heBoundary with heOuter | heInner
      · exact data.boundaryData.houterAmbientBoundarySubset heOuter
      · exact data.boundaryData.hinnerAmbientBoundarySubset heInner⟩

theorem PlanarBoundaryAnnulusRootParentPeelData.roots_subset_boundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb) :
    data.interiorData.roots ⊆
      data.boundaryData.outerBoundaryFaces ∪ data.boundaryData.innerBoundaryFaces := by
  intro f hf
  exact data.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_of_mem_roots hf

/-- Same-embedding constructor from an annulus boundary split and the generic boundary-root
adjacency-distance interior-dual data. Since the generic data roots meet the full selected
boundary and the annulus data covers that selected boundary by the outer/inner split, no
one-sided root choice is needed. -/
def planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryAnnulusRootAdjDistancePeelData emb :=
  { boundaryData := boundaryData
    interiorData := interiorData
    hrootsBoundary := by
      intro r hr
      rcases interiorData.hrootsBoundary r hr with ⟨e, her, heSelected⟩
      exact ⟨e, her, boundaryData.hambientBoundaryCover heSelected⟩ }

/-- Same-embedding constructor from an annulus boundary split and the generic boundary-root
canonical parent interior-dual data. -/
def planarBoundaryAnnulusRootParentPeelData_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryAnnulusRootParentPeelData emb :=
  { boundaryData := boundaryData
    interiorData := interiorData
    hrootsBoundary := by
      intro r hr
      rcases interiorData.hrootsBoundary r hr with ⟨e, her, heSelected⟩
      exact ⟨e, her, boundaryData.hambientBoundaryCover heSelected⟩ }

/-- Closed-walk source constructor for the two-sided annulus-root adjacency-distance package.
The closed-walk source supplies the honest two-component boundary split; the generic interior-dual
data supplies roots meeting the full selected boundary, which the source split covers. -/
noncomputable def planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryAnnulusRootAdjDistancePeelData emb :=
  planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    source.toPlanarBoundaryAnnulusBoundaryData interiorData

/-- Closed-walk source constructor for the two-sided annulus-root parent package. -/
noncomputable def planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryAnnulusRootParentPeelData emb :=
  planarBoundaryAnnulusRootParentPeelData_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
    source.toPlanarBoundaryAnnulusBoundaryData interiorData

theorem exists_root_mem_outerBoundaryFaces_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    ∃ f : AmbientFace emb.faces,
      f ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces ∧
      f ∈ interiorData.roots := by
  let data :=
    planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      source interiorData
  simpa [data] using
    (PlanarBoundaryAnnulusRootAdjDistancePeelData.exists_root_mem_outerBoundaryFaces data)

theorem exists_root_mem_innerBoundaryFaces_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    ∃ f : AmbientFace emb.faces,
      f ∈ source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces ∧
      f ∈ interiorData.roots := by
  let data :=
    planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      source interiorData
  simpa [data] using
    (PlanarBoundaryAnnulusRootAdjDistancePeelData.exists_root_mem_innerBoundaryFaces data)

/-- The canonical source-side root set for the two-sided interior-dual attack: all faces meeting
one of the two ambient boundary components extracted from the honest closed-walk source. -/
noncomputable def PlanarBoundaryClosedWalkAnnulusBoundarySource.boundaryFaceRoots
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb) :
    Finset (AmbientFace emb.faces) :=
  source.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces ∪
    source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces

/-- Every source boundary-face root has a concrete edge on the annulus boundary support extracted
from the same closed-walk source. This is the root-boundary premise needed by the fixed-root
positive constructors below. -/
theorem PlanarBoundaryClosedWalkAnnulusBoundarySource.exists_mem_outerOrInnerAmbientBoundary_of_mem_boundaryFaceRoots
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    {r : AmbientFace emb.faces} (hr : r ∈ source.boundaryFaceRoots) :
    ∃ e ∈ emb.faceBoundary r.1,
      e ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
        source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary := by
  rcases Finset.mem_union.1
      (by
        simpa [PlanarBoundaryClosedWalkAnnulusBoundarySource.boundaryFaceRoots] using hr) with
    hOuter | hInner
  · rcases
      (source.toPlanarBoundaryAnnulusBoundaryData.mem_outerBoundaryFaces_iff).1 hOuter with
      ⟨e, her, heOuter⟩
    exact ⟨e, her, Finset.mem_union.2 (Or.inl heOuter)⟩
  · rcases
      (source.toPlanarBoundaryAnnulusBoundaryData.mem_innerBoundaryFaces_iff).1 hInner with
      ⟨e, her, heInner⟩
    exact ⟨e, her, Finset.mem_union.2 (Or.inr heInner)⟩

/-- Any generic boundary-root interior-dual datum compatible with the selected boundary shows
that the source boundary-face root set covers all interior-dual components.  Thus, after fixing
roots to the source boundary faces, coverage is not the hard part; the nontrivial source-side
burden is separation and the rooted peel data. -/
theorem PlanarBoundaryClosedWalkAnnulusBoundarySource.rootSetCovers_boundaryFaceRoots_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots := by
  intro f
  rcases data.hcoverRoots f with ⟨r, hrRoots, hfr⟩
  refine ⟨r, ?_, hfr⟩
  rcases data.hrootsBoundary r hrRoots with ⟨e, her, heSelected⟩
  have hrBoundary :
      r ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces ∪
        source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces :=
    (source.toPlanarBoundaryAnnulusBoundaryData.mem_outerBoundaryFaces_or_mem_innerBoundaryFaces_iff).2
      ⟨e, her, heSelected⟩
  simpa [PlanarBoundaryClosedWalkAnnulusBoundarySource.boundaryFaceRoots] using hrBoundary

/-- If an outer boundary face can reach an inner boundary face in the interior dual graph, then
the full source boundary-face root set cannot be a separated root set.  This is the direct
source-side obstruction for the fixed-root IDBRAD constructor: all boundary faces can be used as
roots only when the interior dual separates the two boundary-face layers into distinct reachable
components. -/
theorem PlanarBoundaryClosedWalkAnnulusBoundarySource.not_rootSetSeparated_boundaryFaceRoots_of_reachable_outerBoundaryFace_innerBoundaryFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    {fo fi : AmbientFace emb.faces}
    (hfo : fo ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces)
    (hfi : fi ∈ source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces)
    (hreach : (interiorDualGraph emb.faceBoundary emb.faces).Reachable fo fi) :
    ¬ RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots := by
  intro hsep
  have hfoRoot : fo ∈ source.boundaryFaceRoots := by
    exact Finset.mem_union.2 (Or.inl hfo)
  have hfiRoot : fi ∈ source.boundaryFaceRoots := by
    exact Finset.mem_union.2 (Or.inr hfi)
  have hEq : fo = fi := hsep hfoRoot hfiRoot hreach
  have hfi' : fo ∈ source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
    simpa [hEq] using hfi
  exact
    (Finset.disjoint_left.mp source.outerBoundaryFaces_disjoint_innerBoundaryFaces)
      hfo hfi'

/-- A generic boundary-root IDBRAD datum already forces the source's outer and inner boundary-face
layers to lie in different interior-dual reachability components.  Indeed, the datum makes every
source boundary face a root because boundary faces cannot be peeled, and root separatedness then
forbids a path from an outer root to an inner root. -/
theorem PlanarBoundaryClosedWalkAnnulusBoundarySource.not_reachable_outerBoundaryFace_innerBoundaryFace_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    {fo fi : AmbientFace emb.faces}
    (hfo : fo ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces)
    (hfi : fi ∈ source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces) :
    ¬ (interiorDualGraph emb.faceBoundary emb.faces).Reachable fo fi := by
  intro hreach
  let data :=
    planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      source interiorData
  have hfoRoot : fo ∈ interiorData.roots := by
    simpa [data] using
      (PlanarBoundaryAnnulusRootAdjDistancePeelData.mem_roots_of_mem_outerBoundaryFaces
        data hfo)
  have hfiRoot : fi ∈ interiorData.roots := by
    simpa [data] using
      (PlanarBoundaryAnnulusRootAdjDistancePeelData.mem_roots_of_mem_innerBoundaryFaces
        data hfi)
  have hEq : fo = fi := interiorData.hsepRoots hfoRoot hfiRoot hreach
  have hfi' : fo ∈ source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces := by
    simpa [hEq] using hfi
  exact
    (Finset.disjoint_left.mp source.outerBoundaryFaces_disjoint_innerBoundaryFaces)
      hfo hfi'

/-- Existential obstruction form: an honest closed-walk source whose extracted outer and inner
boundary-face layers are connected in the interior dual cannot carry the generic boundary-root
IDBRAD package on the same embedding. -/
theorem PlanarBoundaryClosedWalkAnnulusBoundarySource.not_nonempty_interiorDualBoundaryRootAdjDistancePeelData_of_reachable_outerBoundaryFace_innerBoundaryFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    {fo fi : AmbientFace emb.faces}
    (hfo : fo ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces)
    (hfi : fi ∈ source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces)
    (hreach : (interiorDualGraph emb.faceBoundary emb.faces).Reachable fo fi) :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  rintro ⟨interiorData⟩
  exact
    source.not_reachable_outerBoundaryFace_innerBoundaryFace_of_interiorDualBoundaryRootAdjDistancePeelData
      interiorData hfo hfi hreach

/-- Same-embedding existential obstruction: a closed-walk source, a generic IDBRAD datum, and an
interior-dual path from an extracted outer boundary face to an extracted inner boundary face
cannot coexist. -/
theorem not_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData_and_reachable_outerBoundaryFace_innerBoundaryFace
    {G : SimpleGraph V} :
    ¬ (∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ _interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        ∃ fo fi : AmbientFace emb.faces,
          fo ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces ∧
          fi ∈ source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces ∧
          (interiorDualGraph emb.faceBoundary emb.faces).Reachable fo fi) := by
  rintro ⟨emb, source, interiorData, fo, fi, hfo, hfi, hreach⟩
  exact
    source.not_reachable_outerBoundaryFace_innerBoundaryFace_of_interiorDualBoundaryRootAdjDistancePeelData
      interiorData hfo hfi hreach

/-- Once the source boundary-face roots cover and separate the interior-dual components, the
canonical shortest-path parent map toward those roots is well founded. This isolates the acyclic
orientation part of the sufficiency direction independently of the remaining witness-edge cover
obligations. -/
theorem PlanarBoundaryClosedWalkAnnulusBoundarySource.wellFounded_parentRel_boundaryFaceRoots_parentTowardsRoot
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots) :
    WellFounded (ParentRel
      (parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots))) := by
  let T := interiorDualSpanningForest emb.faceBoundary emb.faces
  let rootFace : AmbientFace emb.faces → AmbientFace emb.faces :=
    interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
      hcoverRoots hsepRoots
  refine wellFounded_parentRel_parentTowardsRoot T rootFace ?_ ?_
  · intro f
    exact
      reachable_interiorDualSpanningForestRoot emb.faceBoundary emb.faces
        source.boundaryFaceRoots hcoverRoots hsepRoots f
  · intro g f hgf
    have hroot : rootFace g = rootFace f := by
      simpa [T, rootFace] using
        interiorDualSpanningForestRoot_eq_of_adj emb.faceBoundary emb.faces
          source.boundaryFaceRoots hcoverRoots hsepRoots
          (parentTowardsRoot_some_adj T rootFace hgf)
    exact hroot.symm

/-- Failed-converse form: if a concrete closed-walk source has an outer-to-inner path in the
interior dual, then no universal same-embedding theorem can derive generic IDBRAD data from the
closed-walk source package. -/
theorem not_forall_interiorDualBoundaryRootAdjDistancePeelData_of_exists_closedWalkAnnulusBoundarySource_and_reachable_outerBoundaryFace_innerBoundaryFace
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
        ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        ∃ fo fi : AmbientFace emb.faces,
          fo ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerBoundaryFaces ∧
          fi ∈ source.toPlanarBoundaryAnnulusBoundaryData.innerBoundaryFaces ∧
          (interiorDualGraph emb.faceBoundary emb.faces).Reachable fo fi) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        PlanarBoundaryClosedWalkAnnulusBoundarySource emb →
          Nonempty (InteriorDualBoundaryRootAdjDistancePeelData
            emb.faces emb.faceBoundary) := by
  intro h
  rcases hWitness with ⟨emb, source, fo, fi, hfo, hfi, hreach⟩
  rcases h (emb := emb) source with ⟨interiorData⟩
  exact
    source.not_reachable_outerBoundaryFace_innerBoundaryFace_of_interiorDualBoundaryRootAdjDistancePeelData
      interiorData hfo hfi hreach

/-- Primitive two-sided rooted constructor from cover/separated roots and rooted shared-edge
face-membership data. The root support is the full annulus boundary split, not only the outer
component. -/
def planarBoundaryAnnulusRootAdjDistancePeelDataOfCoverSeparatedAnnulusBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (peelFaces roots : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ emb.faceBoundary r.1,
        e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary)
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots
                hcoverRoots hsepRoots g))
    (hall : ∀ e, totalIncidenceCount emb.faceBoundary emb.faces e ≤ 2) :
    PlanarBoundaryAnnulusRootAdjDistancePeelData emb :=
  { boundaryData := boundaryData
    interiorData :=
      interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundarySubsetRootsCanonicalRootedSharedEdgeFaceMembershipCover
        (allFaces := emb.faces) (peelFaces := peelFaces) (roots := roots)
        (faceBoundary := emb.faceBoundary)
        (boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary)
        (by
          intro e he
          rcases Finset.mem_union.1 he with heOuter | heInner
          · exact boundaryData.houterAmbientBoundarySubset heOuter
          · exact boundaryData.hinnerAmbientBoundarySubset heInner)
        hunique fallbackEdge hcoverRoots hsepRoots hpeelInterior hrootsBoundary
        hcover hchildren hall
    hrootsBoundary := hrootsBoundary }

/-- Source-facing primitive constructor for the generic interior-dual boundary-root data.  The
closed-walk source supplies the annulus boundary split; the remaining hypotheses are the actual
rooted interior-dual peel obligations: cover/separated roots, boundary-free peeled faces, interior
edge coverage by canonical rooted shared edges, and the child-face membership condition. -/
noncomputable def interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceCoverSeparatedAnnulusBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces roots : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ emb.faceBoundary r.1,
        e ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
          source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary)
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots
                hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots
                hcoverRoots hsepRoots g))
    (hall : ∀ e, totalIncidenceCount emb.faceBoundary emb.faces e ≤ 2) :
    InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary :=
  (planarBoundaryAnnulusRootAdjDistancePeelDataOfCoverSeparatedAnnulusBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover
      source.toPlanarBoundaryAnnulusBoundaryData peelFaces roots hunique fallbackEdge
      hcoverRoots hsepRoots hpeelInterior hrootsBoundary hcover hchildren hall).interiorData

/-- Source-side IDBRAD constructor with the roots and fallback edge fixed by the honest
closed-walk source. The remaining hypotheses are the real geometric burden: the source boundary
faces must cover and separate the interior-dual components, peeled faces must avoid the selected
boundary, every interior edge must be represented by the rooted shared edge of a peeled face, and
non-witness edges must move strictly farther from the source boundary roots. -/
noncomputable def interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
            hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
          e ∈ emb.faceBoundary g.1 ∧
          (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              f (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
              g (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots g)) :
    InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary :=
  interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceCoverSeparatedAnnulusBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover
    source peelFaces source.boundaryFaceRoots hunique source.fallbackEdge
    hcoverRoots hsepRoots hpeelInterior
    (by
      intro r hr
      rcases Finset.mem_union.1
          (by
            simpa [PlanarBoundaryClosedWalkAnnulusBoundarySource.boundaryFaceRoots] using hr) with
        hOuter | hInner
      · rcases
          (source.toPlanarBoundaryAnnulusBoundaryData.mem_outerBoundaryFaces_iff).1 hOuter with
          ⟨e, her, heOuter⟩
        exact ⟨e, her, Finset.mem_union.2 (Or.inl heOuter)⟩
      · rcases
          (source.toPlanarBoundaryAnnulusBoundaryData.mem_innerBoundaryFaces_iff).1 hInner with
          ⟨e, her, heInner⟩
        exact ⟨e, her, Finset.mem_union.2 (Or.inr heInner)⟩)
    hcover hchildren (planeEmbeddingWithBoundary_totalIncidenceCount_le_two emb)

/-- Graph-level source-side constructor for the generic interior-dual boundary-root target.  This
is the positive counterpart to the forcing-edge obstructions: after an honest closed-walk source
is fixed, deriving `InteriorDualBoundaryRootAdjDistancePeelData` is exactly the explicit rooted
peel datum listed in the hypotheses, not a selector-internal obligation. -/
theorem admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_exists_closedWalkAnnulusBoundarySource_and_coverSeparatedAnnulusBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ peelFaces roots : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ fallbackEdge : AmbientFace emb.faces → G.edgeSet,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces) roots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces) roots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        (∀ r ∈ roots,
          ∃ e ∈ emb.faceBoundary r.1,
            e ∈ source.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary ∪
              source.toPlanarBoundaryAnnulusBoundaryData.innerAmbientBoundary) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots
              hcoverRoots hsepRoots)
            fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots
                hcoverRoots hsepRoots)
              fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              (interiorDualSpanningForest emb.faceBoundary emb.faces).Adj f g ∧
              e ∈ emb.faceBoundary g.1 ∧
              (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                  f (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots
                    hcoverRoots hsepRoots f) <
                (interiorDualSpanningForest emb.faceBoundary emb.faces).dist
                  g (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots
                    hcoverRoots hsepRoots g)) ∧
        (∀ e, totalIncidenceCount emb.faceBoundary emb.faces e ≤ 2)) :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G := by
  rcases hG with
    ⟨emb, source, peelFaces, roots, hunique, fallbackEdge, hcoverRoots, hsepRoots,
      hpeelInterior, hrootsBoundary, hcover, hchildren, hall⟩
  exact
    ⟨emb, ⟨
      interiorDualBoundaryRootAdjDistancePeelDataOfClosedWalkAnnulusBoundarySourceCoverSeparatedAnnulusBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover
        source peelFaces roots hunique fallbackEdge hcoverRoots hsepRoots hpeelInterior
        hrootsBoundary hcover hchildren hall⟩⟩

/-- Primitive two-sided rooted constructor for the canonical parent package. -/
def planarBoundaryAnnulusRootParentPeelDataOfCoverSeparatedAnnulusBoundaryRootsCanonicalParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (peelFaces roots : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ emb.faceBoundary r.1,
        e ∈ boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary)
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces roots
                hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1)
    (hall : ∀ e, totalIncidenceCount emb.faceBoundary emb.faces e ≤ 2) :
    PlanarBoundaryAnnulusRootParentPeelData emb :=
  { boundaryData := boundaryData
    interiorData :=
      interiorDualBoundaryRootParentPeelDataOfCoverSeparatedBoundarySubsetRootsCanonicalParentSharedEdgeFaceMembershipCover
        (allFaces := emb.faces) (peelFaces := peelFaces) (roots := roots)
        (faceBoundary := emb.faceBoundary)
        (boundaryData.outerAmbientBoundary ∪ boundaryData.innerAmbientBoundary)
        (by
          intro e he
          rcases Finset.mem_union.1 he with heOuter | heInner
          · exact boundaryData.houterAmbientBoundarySubset heOuter
          · exact boundaryData.hinnerAmbientBoundarySubset heInner)
        hunique fallbackEdge hcoverRoots hsepRoots hpeelInterior hrootsBoundary
      hcover hchildren hall
    hrootsBoundary := hrootsBoundary }

/-- Source-fixed parent constructor for the same sufficiency branch as IDBRAD.  The roots are the
outer-or-inner boundary faces extracted from the closed-walk source, the fallback edge is the
source's facial closed-walk fallback, and the child condition is stated directly for the canonical
shortest-path parent map toward those source roots. -/
noncomputable def planarBoundaryAnnulusRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
            hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1) :
    PlanarBoundaryAnnulusRootParentPeelData emb :=
  planarBoundaryAnnulusRootParentPeelDataOfCoverSeparatedAnnulusBoundaryRootsCanonicalParentSharedEdgeFaceMembershipCover
    source.toPlanarBoundaryAnnulusBoundaryData peelFaces source.boundaryFaceRoots
    hunique source.fallbackEdge hcoverRoots hsepRoots hpeelInterior
    (fun _r hr =>
      source.exists_mem_outerOrInnerAmbientBoundary_of_mem_boundaryFaceRoots hr)
    hcover hchildren (planeEmbeddingWithBoundary_totalIncidenceCount_le_two emb)

/-- Interior-dual payload of the source-fixed parent constructor. This is the parent-oriented
equivalent of constructing IDBRAD from the same closed-walk source boundary-order roots. -/
noncomputable def interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
            hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1) :
    InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary :=
  (planarBoundaryAnnulusRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
    source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren).interiorData

/-- Source-fixed IDBRAD payload from the raw canonical-parent shared-edge cover.  The local
child-membership condition is constructed by the generic two-incidence reduction, so the
remaining nondegenerate source burden is the boundary-root cover/separation data, boundary-free
peeled faces, and the rooted shared-edge cover of the interior support. -/
noncomputable def interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge)) :
    InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary :=
  interiorDualBoundaryRootParentPeelDataOfCoverSeparatedBoundaryRootsCanonicalParentSharedEdgeCover
    (allFaces := emb.faces) (peelFaces := peelFaces) (roots := source.boundaryFaceRoots)
    (faceBoundary := emb.faceBoundary) hunique source.fallbackEdge hcoverRoots hsepRoots
    hpeelInterior
    (by
      intro r hr
      rcases source.exists_mem_outerOrInnerAmbientBoundary_of_mem_boundaryFaceRoots hr with
        ⟨e, her, heBoundary⟩
      refine ⟨e, her, ?_⟩
      rcases Finset.mem_union.1 heBoundary with heOuter | heInner
      · exact source.toPlanarBoundaryAnnulusBoundaryData.houterAmbientBoundarySubset heOuter
      · exact source.toPlanarBoundaryAnnulusBoundaryData.hinnerAmbientBoundarySubset heInner)
    hcover
    (planeEmbeddingWithBoundary_totalIncidenceCount_le_two emb)

/-- Source-fixed nondegenerate witness for the canonical-parent cover.  Under the raw
closed-walk annulus source hypotheses used by the parent constructor, every covered interior edge
is realized by a peeled non-root face with an actual shortest-path parent toward the source roots.
This isolates the nonempty-interior branch from the fallback-edge branch of the canonical edge
selector. -/
theorem exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_mem_interiorEdgeSupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ∃ f ∈ peelFaces,
      f ≠ interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
        hcoverRoots hsepRoots f ∧
      (∃ p,
        parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
            hcoverRoots hsepRoots) f = some p) ∧
      rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
            hcoverRoots hsepRoots)
          source.fallbackEdge f = e ∧
      e ∈ emb.faceBoundary f.1 := by
  exact
    exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_canonicalParentCover_of_mem_interiorEdgeSupport
      emb.faceBoundary emb.faces peelFaces source.boundaryFaceRoots hunique source.fallbackEdge
      hcoverRoots hsepRoots hpeelInterior
      (by
        intro r hr
        rcases source.exists_mem_outerOrInnerAmbientBoundary_of_mem_boundaryFaceRoots hr with
          ⟨e, her, heBoundary⟩
        refine ⟨e, her, ?_⟩
        rcases Finset.mem_union.1 heBoundary with heOuter | heInner
        · exact source.toPlanarBoundaryAnnulusBoundaryData.houterAmbientBoundarySubset heOuter
        · exact source.toPlanarBoundaryAnnulusBoundaryData.hinnerAmbientBoundarySubset heInner)
      hcover he

/-- Nonempty-support source-fixed form of the canonical-parent nondegenerate witness.  If the
interior-edge support is nonempty, the raw closed-walk source hypotheses for the parent
constructor produce an actual peeled non-root face, a real parent, and the corresponding interior
edge on that face. -/
theorem exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_interiorEdgeSupport_nonempty
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots)
        source.fallbackEdge))
    (hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty) :
    ∃ e ∈ interiorEdgeSupport emb.faceBoundary emb.faces,
      ∃ f ∈ peelFaces,
        f ≠ interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
          hcoverRoots hsepRoots f ∧
        (∃ p,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots) f = some p) ∧
        rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge f = e ∧
        e ∈ emb.faceBoundary f.1 := by
  rcases hInterior with ⟨e, he⟩
  rcases
      exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_mem_interiorEdgeSupport
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover he with
    ⟨f, hfPeel, hfNonroot, hfParent, hfe, hef⟩
  exact ⟨e, he, f, hfPeel, hfNonroot, hfParent, hfe, hef⟩

/-- Empty-interior-edge base case for the source-fixed parent package.  Once the closed-walk
source boundary-face roots cover and separate the interior dual, and there are no interior edges
left to cover, the strongest current parent-oriented IDBRAD replacement is inhabited by the
empty peel set.  This is the constructive sanity endpoint for degenerate source components; the
nondegenerate burden remains the rooted shared-edge cover of actual interior edges. -/
noncomputable def interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hnoInterior :
      interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary :=
  interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
    source ∅
    (pairwiseUniqueSharedInteriorEdges_of_interiorEdgeSupport_eq_empty
      emb.faceBoundary emb.faces hnoInterior)
    hcoverRoots hsepRoots
    (by
      intro f hf
      simp at hf)
    (by
      intro e he
      simp [hnoInterior] at he)

/-- Graph-level empty-interior-edge base case for the source-fixed parent sufficiency branch. -/
theorem admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G := by
  rcases hG with
    ⟨emb, source, hcoverRoots, hsepRoots, hnoInterior⟩
  exact
    ⟨emb,
      ⟨interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
        source hcoverRoots hsepRoots hnoInterior⟩⟩

/-- Graph-level source-fixed constructor for the parent-oriented sufficiency branch.  This is the
well-founded-orientation counterpart of the fixed-root IDBRAD constructor: the source fixes the
root set and fallback edge, while the hypotheses state cover/separation, boundary-free peeled
faces, rooted shared-edge coverage, and child membership for the canonical parent map. -/
theorem admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots)
              source.fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
              e ∈ emb.faceBoundary g.1)) :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover, hchildren⟩
  exact
    ⟨emb, ⟨
      interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren⟩⟩

/-- Graph-level source-fixed constructor from the raw canonical-parent shared-edge cover.  The
local parent child-membership condition is derived internally from the cover and the embedding's
two-incidence theorem. -/
theorem admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces source.boundaryFaceRoots
              hcoverRoots hsepRoots)
            source.fallbackEdge)) :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    ⟨emb, ⟨
      interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover⟩⟩

/-- The old outer-boundary-root package is a specialization of the two-sided annulus-root package.
-/
def PlanarBoundaryOuterBoundaryRootAdjDistancePeelData.toPlanarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb) :
    PlanarBoundaryAnnulusRootAdjDistancePeelData emb :=
  { boundaryData := data.boundaryData
    interiorData := data.interiorData
    hrootsBoundary := by
      intro r hr
      rcases data.hrootsOuterBoundary r hr with ⟨e, her, heOuter⟩
      exact ⟨e, her, Finset.mem_union.2 (Or.inl heOuter)⟩ }

/-- The old outer-boundary-root parent package is a specialization of the two-sided annulus-root
parent package. -/
def PlanarBoundaryOuterBoundaryRootParentPeelData.toPlanarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootParentPeelData emb) :
    PlanarBoundaryAnnulusRootParentPeelData emb :=
  { boundaryData := data.boundaryData
    interiorData := data.interiorData
    hrootsBoundary := by
      intro r hr
      rcases data.hrootsOuterBoundary r hr with ⟨e, her, heOuter⟩
      exact ⟨e, her, Finset.mem_union.2 (Or.inl heOuter)⟩ }

/-- Graph-level lowering from a same-embedding annulus boundary split plus generic boundary-root
adjacency-distance data to the two-sided annulus-root target. -/
theorem admitsPlanarBoundaryAnnulusRootAdjDistancePeelData_of_exists_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData G := by
  rcases hG with ⟨emb, boundaryData, ⟨interiorData⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryAnnulusRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData⟩⟩

/-- Graph-level lowering from a same-embedding annulus boundary split plus generic boundary-root
parent data to the two-sided annulus-root parent target. -/
theorem admitsPlanarBoundaryAnnulusRootParentPeelData_of_exists_boundaryData_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
        Nonempty (InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAnnulusRootParentPeelData G := by
  rcases hG with ⟨emb, boundaryData, ⟨interiorData⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryAnnulusRootParentPeelData_of_boundaryData_and_interiorDualBoundaryRootParentPeelData
      boundaryData interiorData⟩⟩

/-- Graph-level closed-walk-source lowering into the two-sided annulus-root adjacency-distance
target. This is the positive companion to the all-outer-root closed-walk obstruction. -/
theorem admitsPlanarBoundaryAnnulusRootAdjDistancePeelData_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData G := by
  rcases hG with ⟨emb, source, ⟨interiorData⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryAnnulusRootAdjDistancePeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootAdjDistancePeelData
      source interiorData⟩⟩

/-- Graph-level closed-walk-source lowering into the two-sided annulus-root parent target. -/
theorem admitsPlanarBoundaryAnnulusRootParentPeelData_of_exists_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
        Nonempty (InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAnnulusRootParentPeelData G := by
  rcases hG with ⟨emb, source, ⟨interiorData⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryAnnulusRootParentPeelData_of_closedWalkAnnulusBoundarySource_and_interiorDualBoundaryRootParentPeelData
      source interiorData⟩⟩

/-- Forgetting the annulus boundary split recovers the generic boundary-root adjacency-distance
target already used by the Theorem 4.9 pipeline. -/
theorem admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_admitsPlanarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.interiorData⟩⟩

/-- The two-sided adjacency-distance package canonically induces the two-sided canonical parent
package. -/
theorem admitsPlanarBoundaryAnnulusRootParentPeelData_of_admitsPlanarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryAnnulusRootParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    { boundaryData := data.boundaryData
      interiorData := data.interiorData.toInteriorDualBoundaryRootParentPeelData
      hrootsBoundary := data.hrootsBoundary }⟩⟩

/-- Forgetting the annulus boundary split recovers the generic boundary-root parent target already
used by the Theorem 4.9 pipeline. -/
theorem admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_admitsPlanarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusRootParentPeelData G) :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.interiorData⟩⟩

/-- Forgetting the interior-dual payload keeps the ambient annulus boundary split. -/
theorem admitsPlanarBoundaryAnnulusBoundaryData_of_admitsPlanarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryAnnulusBoundaryData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.boundaryData⟩⟩

/-- Outer-boundary-root data lowers to the two-sided annulus-root target. -/
theorem admitsPlanarBoundaryAnnulusRootAdjDistancePeelData_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryAnnulusRootAdjDistancePeelData⟩⟩

/-- Outer-boundary-root parent data lowers to the two-sided annulus-root parent target. -/
theorem admitsPlanarBoundaryAnnulusRootParentPeelData_of_admitsPlanarBoundaryOuterBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootParentPeelData G) :
    AdmitsPlanarBoundaryAnnulusRootParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryAnnulusRootParentPeelData⟩⟩

/-- The two-sided annulus-root adjacency-distance package lies on the existing collar-layer proof
route after forgetting only the extra boundary-split bookkeeping. -/
theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G :=
  admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_admitsPlanarBoundaryAnnulusRootAdjDistancePeelData
      hG)

/-- The two-sided annulus-root parent package lies on the existing collar-layer proof route after
forgetting only the extra boundary-split bookkeeping. -/
theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusRootParentPeelData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G :=
  admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
    (admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_admitsPlanarBoundaryAnnulusRootParentPeelData
      hG)

end Mettapedia.GraphTheory.FourColor
