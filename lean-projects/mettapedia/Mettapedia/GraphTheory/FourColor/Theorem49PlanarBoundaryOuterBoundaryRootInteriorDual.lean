import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusBoundary
import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusBoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryAnnulusDecomposition
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryInteriorDual

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Annulus-side version of the weakest current interior-dual Step 2 package, with the extra
information that every chosen root face meets the distinguished outer ambient boundary component
rather than merely some undifferentiated ambient boundary edge. This is the paper-facing
"rooted on the outer boundary" specialization of the existing boundary-root adjacency-distance
interface. -/
structure PlanarBoundaryOuterBoundaryRootAdjDistancePeelData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  boundaryData : PlanarBoundaryAnnulusBoundaryData emb
  interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary
  hrootsOuterBoundary : ∀ r ∈ interiorData.roots,
    ∃ e ∈ emb.faceBoundary r.1, e ∈ boundaryData.outerAmbientBoundary

/-- Annulus-side version of the strongest current boundary-root parent package, with the extra
information that every chosen root face meets the distinguished outer ambient boundary component.
This keeps the canonical `parentTowardsRoot` relation while retaining the paper-facing outer-
boundary localization of the root set. -/
structure PlanarBoundaryOuterBoundaryRootParentPeelData {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  boundaryData : PlanarBoundaryAnnulusBoundaryData emb
  interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary
  hrootsOuterBoundary : ∀ r ∈ interiorData.roots,
    ∃ e ∈ emb.faceBoundary r.1, e ∈ boundaryData.outerAmbientBoundary

/-- Graph-level existence form of the annulus-side outer-boundary-rooted interior-dual target. -/
def AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)

/-- Graph-level existence form of the annulus-side outer-boundary-rooted canonical parent target. -/
def AdmitsPlanarBoundaryOuterBoundaryRootParentPeelData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryOuterBoundaryRootParentPeelData emb)

theorem PlanarBoundaryOuterBoundaryRootAdjDistancePeelData.mem_outerBoundaryFaces_of_mem_roots
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.interiorData.roots) :
    f ∈ data.boundaryData.outerBoundaryFaces := by
  rcases data.hrootsOuterBoundary f hf with ⟨e, hef, heOuter⟩
  exact (data.boundaryData.mem_outerBoundaryFaces_iff).2 ⟨e, hef, heOuter⟩

theorem PlanarBoundaryOuterBoundaryRootAdjDistancePeelData.roots_subset_outerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb) :
    data.interiorData.roots ⊆ data.boundaryData.outerBoundaryFaces := by
  intro f hf
  exact data.mem_outerBoundaryFaces_of_mem_roots hf

theorem PlanarBoundaryOuterBoundaryRootAdjDistancePeelData.mem_outerBoundaryFaces_of_not_mem_peelFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∉ data.interiorData.peelFaces) :
    f ∈ data.boundaryData.outerBoundaryFaces := by
  exact data.mem_outerBoundaryFaces_of_mem_roots
    (data.interiorData.mem_roots_of_not_mem_peelFaces hf)

theorem
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelData.exists_mem_selectedBoundarySupport_of_not_mem_peelFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∉ data.interiorData.peelFaces) :
    ∃ e ∈ emb.faceBoundary f.1,
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  rcases (data.boundaryData.mem_outerBoundaryFaces_iff).1
      (data.mem_outerBoundaryFaces_of_not_mem_peelFaces hf) with ⟨e, hef, heOuter⟩
  exact ⟨e, hef, data.boundaryData.houterAmbientBoundarySubset heOuter⟩

theorem PlanarBoundaryOuterBoundaryRootAdjDistancePeelData.not_mem_peelFaces_of_mem_innerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.boundaryData.innerBoundaryFaces) :
    f ∉ data.interiorData.peelFaces := by
  intro hfPeel
  rcases (data.boundaryData.mem_innerBoundaryFaces_iff).1 hf with ⟨e, hef, heInner⟩
  exact (Finset.disjoint_left.mp (data.interiorData.hpeelInterior f hfPeel))
    hef (data.boundaryData.hinnerAmbientBoundarySubset heInner)

theorem PlanarBoundaryOuterBoundaryRootAdjDistancePeelData.mem_outerBoundaryFaces_of_mem_innerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.boundaryData.innerBoundaryFaces) :
    f ∈ data.boundaryData.outerBoundaryFaces := by
  exact data.mem_outerBoundaryFaces_of_not_mem_peelFaces
    (data.not_mem_peelFaces_of_mem_innerBoundaryFaces hf)

theorem PlanarBoundaryOuterBoundaryRootAdjDistancePeelData.innerBoundaryFaces_subset_outerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb) :
    data.boundaryData.innerBoundaryFaces ⊆ data.boundaryData.outerBoundaryFaces := by
  intro f hf
  exact data.mem_outerBoundaryFaces_of_mem_innerBoundaryFaces hf

theorem
    false_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hrootsOuterBoundary : ∀ r ∈ interiorData.roots,
      ∃ e ∈ emb.faceBoundary r.1,
        e ∈ boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary)
    (hreach : ∀ f : AmbientFace emb.faces,
      BoundaryComponentReachableOnFace (emb := emb) f) :
    False := by
  let data :=
    ({ boundaryData := boundaryData.toPlanarBoundaryAnnulusBoundaryData
       interiorData := interiorData
       hrootsOuterBoundary := hrootsOuterBoundary } :
      PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
  rcases data.boundaryData.innerBoundaryFaces_nonempty with ⟨f, hfInner⟩
  have hfOuter : f ∈ data.boundaryData.outerBoundaryFaces :=
    data.mem_outerBoundaryFaces_of_mem_innerBoundaryFaces hfInner
  exact
    (Finset.disjoint_left.mp
      (boundaryData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
        hreach))
      hfOuter hfInner

theorem PlanarBoundaryOuterBoundaryRootParentPeelData.mem_outerBoundaryFaces_of_mem_roots
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootParentPeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.interiorData.roots) :
    f ∈ data.boundaryData.outerBoundaryFaces := by
  rcases data.hrootsOuterBoundary f hf with ⟨e, hef, heOuter⟩
  exact (data.boundaryData.mem_outerBoundaryFaces_iff).2 ⟨e, hef, heOuter⟩

theorem PlanarBoundaryOuterBoundaryRootParentPeelData.roots_subset_outerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootParentPeelData emb) :
    data.interiorData.roots ⊆ data.boundaryData.outerBoundaryFaces := by
  intro f hf
  exact data.mem_outerBoundaryFaces_of_mem_roots hf

theorem PlanarBoundaryOuterBoundaryRootParentPeelData.mem_outerBoundaryFaces_of_not_mem_peelFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootParentPeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∉ data.interiorData.peelFaces) :
    f ∈ data.boundaryData.outerBoundaryFaces := by
  exact data.mem_outerBoundaryFaces_of_mem_roots
    (data.interiorData.mem_roots_of_not_mem_peelFaces hf)

theorem
    PlanarBoundaryOuterBoundaryRootParentPeelData.exists_mem_selectedBoundarySupport_of_not_mem_peelFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootParentPeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∉ data.interiorData.peelFaces) :
    ∃ e ∈ emb.faceBoundary f.1,
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  rcases (data.boundaryData.mem_outerBoundaryFaces_iff).1
      (data.mem_outerBoundaryFaces_of_not_mem_peelFaces hf) with ⟨e, hef, heOuter⟩
  exact ⟨e, hef, data.boundaryData.houterAmbientBoundarySubset heOuter⟩

theorem PlanarBoundaryOuterBoundaryRootParentPeelData.not_mem_peelFaces_of_mem_innerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootParentPeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.boundaryData.innerBoundaryFaces) :
    f ∉ data.interiorData.peelFaces := by
  intro hfPeel
  rcases (data.boundaryData.mem_innerBoundaryFaces_iff).1 hf with ⟨e, hef, heInner⟩
  exact (Finset.disjoint_left.mp (data.interiorData.hpeelInterior f hfPeel))
    hef (data.boundaryData.hinnerAmbientBoundarySubset heInner)

theorem PlanarBoundaryOuterBoundaryRootParentPeelData.mem_outerBoundaryFaces_of_mem_innerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootParentPeelData emb)
    {f : AmbientFace emb.faces} (hf : f ∈ data.boundaryData.innerBoundaryFaces) :
    f ∈ data.boundaryData.outerBoundaryFaces := by
  exact data.mem_outerBoundaryFaces_of_not_mem_peelFaces
    (data.not_mem_peelFaces_of_mem_innerBoundaryFaces hf)

theorem PlanarBoundaryOuterBoundaryRootParentPeelData.innerBoundaryFaces_subset_outerBoundaryFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootParentPeelData emb) :
    data.boundaryData.innerBoundaryFaces ⊆ data.boundaryData.outerBoundaryFaces := by
  intro f hf
  exact data.mem_outerBoundaryFaces_of_mem_innerBoundaryFaces hf

theorem
    false_of_boundaryReachabilityData_and_interiorDualBoundaryRootParentPeelData_of_rootsOuterAmbientBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hrootsOuterBoundary : ∀ r ∈ interiorData.roots,
      ∃ e ∈ emb.faceBoundary r.1,
        e ∈ boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary)
    (hreach : ∀ f : AmbientFace emb.faces,
      BoundaryComponentReachableOnFace (emb := emb) f) :
    False := by
  let data :=
    ({ boundaryData := boundaryData.toPlanarBoundaryAnnulusBoundaryData
       interiorData := interiorData
       hrootsOuterBoundary := hrootsOuterBoundary } :
      PlanarBoundaryOuterBoundaryRootParentPeelData emb)
  rcases data.boundaryData.innerBoundaryFaces_nonempty with ⟨f, hfInner⟩
  have hfOuter : f ∈ data.boundaryData.outerBoundaryFaces :=
    data.mem_outerBoundaryFaces_of_mem_innerBoundaryFaces hfInner
  exact
    (Finset.disjoint_left.mp
      (boundaryData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
        hreach))
      hfOuter hfInner

theorem
    false_of_boundaryReachabilityData_and_interiorDualBoundaryRootParentPeelData_of_rootsOuterAmbientBoundary_and_boundarySelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hrootsOuterBoundary : ∀ r ∈ interiorData.roots,
      ∃ e ∈ emb.faceBoundary r.1,
        e ∈ boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f) :
    False := by
  exact
    false_of_boundaryReachabilityData_and_interiorDualBoundaryRootParentPeelData_of_rootsOuterAmbientBoundary
      boundaryData interiorData hrootsOuterBoundary
      (fun f =>
        boundaryComponentReachableOnFace_of_boundarySelectedBoundaryArcOnFace
          (harc f))

theorem
    not_exists_planarBoundaryOuterBoundaryRootAdjDistancePeelData_sameBoundaryData_of_boundaryReachabilityData_and_boundarySelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f) :
    ¬ ∃ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        data.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  rintro ⟨data, hboundary⟩
  exact
    false_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary
      boundaryData data.interiorData
      (by
        intro r hr
        rcases data.hrootsOuterBoundary r hr with ⟨e, her, heOuter⟩
        exact ⟨e, her, by simpa [hboundary] using heOuter⟩)
      (fun f =>
        boundaryComponentReachableOnFace_of_boundarySelectedBoundaryArcOnFace
          (harc f))

theorem
    not_exists_planarBoundaryOuterBoundaryRootParentPeelData_sameBoundaryData_of_boundaryReachabilityData_and_boundarySelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f) :
    ¬ ∃ data : PlanarBoundaryOuterBoundaryRootParentPeelData emb,
        data.boundaryData = boundaryData.toPlanarBoundaryAnnulusBoundaryData := by
  rintro ⟨data, hboundary⟩
  exact
    false_of_boundaryReachabilityData_and_interiorDualBoundaryRootParentPeelData_of_rootsOuterAmbientBoundary_and_boundarySelectedBoundaryArcOnFace
      boundaryData data.interiorData
      (by
        intro r hr
        rcases data.hrootsOuterBoundary r hr with ⟨e, her, heOuter⟩
        exact ⟨e, her, by simpa [hboundary] using heOuter⟩)
      harc

/-- Constructor for the annulus-side outer-boundary-rooted package from the generic
boundary-subset-rooted interior-dual data. This is the direct bridge from a distinguished
outer annulus boundary support to the live Step 2 interior-dual endpoint. -/
def
    planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hrootsOuterBoundary : ∀ r ∈ interiorData.roots,
      ∃ e ∈ emb.faceBoundary r.1, e ∈ boundaryData.outerAmbientBoundary) :
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb :=
  { boundaryData := boundaryData
    interiorData := interiorData
    hrootsOuterBoundary := hrootsOuterBoundary }

/-- Same-embedding constructor from an actual annulus decomposition and live interior-dual
adjacency-distance peel data. The only extra hypothesis is the geometric one that each chosen root
face meets the outer annulus cycle `Γ₀`, which the decomposition identifies with the distinguished
outer ambient boundary. -/
def
    planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_annulusDecomposition_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (decomp : PlanarBoundaryAnnulusDecomposition emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hrootsBoundaryCycleZero : ∀ r ∈ interiorData.roots,
      ∃ e ∈ emb.faceBoundary r.1, e ∈ decomp.boundaryCycle 0) :
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb :=
  planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    decomp.toPlanarBoundaryAnnulusBoundaryData interiorData
    (by
      intro r hr
      rcases hrootsBoundaryCycleZero r hr with ⟨e, her, he0⟩
      refine ⟨e, her, ?_⟩
      simpa [decomp.boundaryCycle_zero_eq_outerAmbientBoundary] using he0)

/-- Graph-level lowering from an abstract annulus boundary split plus the live interior-dual
adjacency-distance peel data, under the geometric hypothesis that each chosen root face meets the
distinguished outer ambient boundary of that split. -/
theorem
    admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_of_exists_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData_and_rootsOuterBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        ∀ r ∈ interiorData.roots,
          ∃ e ∈ emb.faceBoundary r.1, e ∈ boundaryData.outerAmbientBoundary) :
    AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G := by
  rcases hG with ⟨emb, boundaryData, interiorData, hrootsOuterBoundary⟩
  exact ⟨emb, ⟨
    planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData hrootsOuterBoundary⟩⟩

/-- Graph-level lowering from an actual annulus decomposition and live interior-dual
adjacency-distance peel data, under the geometric hypothesis that each chosen root face meets the
outer annulus cycle `Γ₀`. -/
theorem
    admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_of_exists_annulusDecomposition_and_interiorDualBoundaryRootAdjDistancePeelData_and_rootsBoundaryCycleZero
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ decomp : PlanarBoundaryAnnulusDecomposition emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        ∀ r ∈ interiorData.roots,
          ∃ e ∈ emb.faceBoundary r.1, e ∈ decomp.boundaryCycle 0) :
    AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G := by
  rcases hG with ⟨emb, decomp, interiorData, hrootsBoundaryCycleZero⟩
  exact ⟨emb, ⟨
    planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_annulusDecomposition_and_interiorDualBoundaryRootAdjDistancePeelData
      decomp interiorData hrootsBoundaryCycleZero⟩⟩

/-- Constructor for the annulus-side outer-boundary-rooted package from the generic
boundary-subset-rooted interior-dual data. This is the direct bridge from a distinguished
outer annulus boundary support to the live Step 2 interior-dual endpoint. -/
def
    planarBoundaryOuterBoundaryRootAdjDistancePeelDataOfCoverSeparatedOuterBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover
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
    (hrootsOuterBoundary : ∀ r ∈ roots,
      ∃ e ∈ emb.faceBoundary r.1, e ∈ boundaryData.outerAmbientBoundary)
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
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb :=
  { boundaryData := boundaryData
    interiorData :=
      interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundarySubsetRootsCanonicalRootedSharedEdgeFaceMembershipCover
        (allFaces := emb.faces) (peelFaces := peelFaces) (roots := roots)
        (faceBoundary := emb.faceBoundary)
        boundaryData.outerAmbientBoundary boundaryData.houterAmbientBoundarySubset
        hunique fallbackEdge hcoverRoots hsepRoots hpeelInterior hrootsOuterBoundary
        hcover hchildren hall
    hrootsOuterBoundary := hrootsOuterBoundary }

/-- The same primitive rooted constructor specialized to an actual annulus decomposition. This lets
geometry work directly with the outer cycle `Γ₀` rather than first repackaging it as an abstract
outer ambient boundary support. -/
def
    planarBoundaryOuterBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundaryCycleZeroRootsCanonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (decomp : PlanarBoundaryAnnulusDecomposition emb)
    (peelFaces roots : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hrootsBoundaryCycleZero : ∀ r ∈ roots,
      ∃ e ∈ emb.faceBoundary r.1, e ∈ decomp.boundaryCycle 0)
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
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb :=
  planarBoundaryOuterBoundaryRootAdjDistancePeelDataOfCoverSeparatedOuterBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover
    decomp.toPlanarBoundaryAnnulusBoundaryData peelFaces roots hunique fallbackEdge
    hcoverRoots hsepRoots hpeelInterior
    (by
      intro r hr
      rcases hrootsBoundaryCycleZero r hr with ⟨e, her, he0⟩
      refine ⟨e, her, ?_⟩
      simpa [decomp.boundaryCycle_zero_eq_outerAmbientBoundary] using he0)
    hcover hchildren hall

/-- Same-embedding constructor from a concrete shared-endpoint boundary-component witness and the
live interior-dual boundary-root adjacency-distance package. The extra hypothesis localizes each
chosen root face to the reachability component of `outerRoot`, so the abstract outer annulus
boundary support is recovered from honest boundary-edge connectivity rather than postulated
separately. -/
noncomputable def
    planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hrootsOuterBoundaryComponent : ∀ r ∈ interiorData.roots,
      ∃ e : PlanarBoundaryEdgeVertex emb,
        e.1 ∈ emb.faceBoundary r.1 ∧
        uniqueReachableRoot
            (planarBoundarySupportEndpointAdjGraph emb)
            boundaryData.rootSet boundaryData.hasUniqueReachableRoot e =
          boundaryData.outerRoot) :
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb := by
  refine
    { boundaryData := boundaryData.toPlanarBoundaryAnnulusBoundaryData
      interiorData := interiorData
      hrootsOuterBoundary := ?_ }
  intro r hr
  rcases hrootsOuterBoundaryComponent r hr with ⟨e, her, heroot⟩
  exact ⟨e.1, her,
    boundaryData.mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData heroot⟩

/-- Same-embedding constructor from concrete boundary-component reachability data and live
interior-dual adjacency-distance peel data, under the more geometric hypothesis that each chosen
root face meets the extracted outer ambient boundary itself. The component-equality witness is then
recovered internally from the reachability-based boundary split. -/
noncomputable def
    planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hrootsOuterBoundary : ∀ r ∈ interiorData.roots,
      ∃ e ∈ emb.faceBoundary r.1,
        e ∈ boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) :
    PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb :=
  planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData
    (by
      intro r hr
      rcases hrootsOuterBoundary r hr with ⟨e, her, heOuter⟩
      refine ⟨⟨e, boundaryData.toPlanarBoundaryAnnulusBoundaryData.houterAmbientBoundarySubset
        heOuter⟩, her, ?_⟩
      exact
        boundaryData.uniqueReachableRoot_eq_outerRoot_of_mem_outerAmbientBoundary_toPlanarBoundaryAnnulusBoundaryData
          heOuter)

/-- Graph-level lowering from concrete same-embedding boundary-component reachability data and
live interior-dual adjacency-distance peel data to the paper-facing outer-boundary-root annulus
target. The only extra local witness says that each chosen root face meets a boundary edge in the
shared-endpoint component of `outerRoot`. -/
theorem
    admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_rootsOuterBoundaryComponent
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        ∀ r ∈ interiorData.roots,
          ∃ e : PlanarBoundaryEdgeVertex emb,
            e.1 ∈ emb.faceBoundary r.1 ∧
            uniqueReachableRoot
                (planarBoundarySupportEndpointAdjGraph emb)
                boundaryData.rootSet boundaryData.hasUniqueReachableRoot e =
              boundaryData.outerRoot) :
    AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G := by
  rcases hG with ⟨emb, boundaryData, interiorData, hrootsOuterBoundaryComponent⟩
  exact ⟨emb, ⟨
    planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData hrootsOuterBoundaryComponent⟩⟩

/-- Graph-level lowering from concrete same-embedding boundary-component reachability data and
live interior-dual adjacency-distance peel data, under the weaker and more geometric hypothesis
that every chosen root face meets the extracted outer ambient boundary. -/
theorem
    admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_rootsOuterAmbientBoundary
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        ∀ r ∈ interiorData.roots,
          ∃ e ∈ emb.faceBoundary r.1,
            e ∈ boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary) :
    AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G := by
  rcases hG with ⟨emb, boundaryData, interiorData, hrootsOuterBoundary⟩
  exact ⟨emb, ⟨
    planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary
      boundaryData interiorData hrootsOuterBoundary⟩⟩

/-- Constructor for the annulus-side outer-boundary-rooted canonical parent package from the
generic boundary-subset-rooted interior-dual parent data. -/
def
    planarBoundaryOuterBoundaryRootParentPeelDataOfCoverSeparatedOuterBoundaryRootsCanonicalParentSharedEdgeFaceMembershipCover
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
    (hrootsOuterBoundary : ∀ r ∈ roots,
      ∃ e ∈ emb.faceBoundary r.1, e ∈ boundaryData.outerAmbientBoundary)
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
    PlanarBoundaryOuterBoundaryRootParentPeelData emb :=
  { boundaryData := boundaryData
    interiorData :=
      interiorDualBoundaryRootParentPeelDataOfCoverSeparatedBoundarySubsetRootsCanonicalParentSharedEdgeFaceMembershipCover
        (allFaces := emb.faces) (peelFaces := peelFaces) (roots := roots)
        (faceBoundary := emb.faceBoundary)
        boundaryData.outerAmbientBoundary boundaryData.houterAmbientBoundarySubset
        hunique fallbackEdge hcoverRoots hsepRoots hpeelInterior hrootsOuterBoundary
        hcover hchildren hall
    hrootsOuterBoundary := hrootsOuterBoundary }

/-- The same primitive parent constructor specialized to an actual annulus decomposition. This
keeps the strongest current parent-based interface phrased directly in terms of the geometric outer
cycle `Γ₀`. -/
def
    planarBoundaryOuterBoundaryRootParentPeelDataOfCoverSeparatedBoundaryCycleZeroRootsCanonicalParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (decomp : PlanarBoundaryAnnulusDecomposition emb)
    (peelFaces roots : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (fallbackEdge : AmbientFace emb.faces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hrootsBoundaryCycleZero : ∀ r ∈ roots,
      ∃ e ∈ emb.faceBoundary r.1, e ∈ decomp.boundaryCycle 0)
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
    PlanarBoundaryOuterBoundaryRootParentPeelData emb :=
  planarBoundaryOuterBoundaryRootParentPeelDataOfCoverSeparatedOuterBoundaryRootsCanonicalParentSharedEdgeFaceMembershipCover
    decomp.toPlanarBoundaryAnnulusBoundaryData peelFaces roots hunique fallbackEdge
    hcoverRoots hsepRoots hpeelInterior
    (by
      intro r hr
      rcases hrootsBoundaryCycleZero r hr with ⟨e, her, he0⟩
      refine ⟨e, her, ?_⟩
      simpa [decomp.boundaryCycle_zero_eq_outerAmbientBoundary] using he0)
    hcover hchildren hall

/-- Forgetting that the roots lie on the distinguished outer boundary recovers the existing
annulus-side boundary-root adjacency-distance package. -/
theorem
    admitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootAdjDistancePeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.interiorData⟩⟩

/-- The outer-boundary-rooted adjacency-distance package canonically induces the outer-boundary-
rooted canonical parent package. -/
theorem
    admitsPlanarBoundaryOuterBoundaryRootParentPeelData_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryOuterBoundaryRootParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    { boundaryData := data.boundaryData
      interiorData := data.interiorData.toInteriorDualBoundaryRootParentPeelData
      hrootsOuterBoundary := data.hrootsOuterBoundary }⟩⟩

/-- Forgetting only the outer-boundary localization keeps the strongest current boundary-root
parent package on the annulus side. -/
theorem
    admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_admitsPlanarBoundaryOuterBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootParentPeelData G) :
    AdmitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.interiorData⟩⟩

/-- Forgetting the interior-dual payload keeps the distinguished annulus boundary split. -/
theorem admitsPlanarBoundaryAnnulusBoundaryData_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryAnnulusBoundaryData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.boundaryData⟩⟩

/-- The outer-boundary-rooted annulus target already lies on the current finite-collar proof
route, by forgetting only the extra root-localization information. -/
theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
      (admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_admitsPlanarBoundaryOuterBoundaryRootParentPeelData
        (admitsPlanarBoundaryOuterBoundaryRootParentPeelData_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
          hG))

/-- The outer-boundary-rooted canonical parent target already lies on the current finite-collar
proof route, by forgetting only the extra root-localization information. -/
theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryOuterBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootParentPeelData G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G :=
  admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData
    (admitsPlanarBoundaryInteriorDualBoundaryRootParentPeelData_of_admitsPlanarBoundaryOuterBoundaryRootParentPeelData
      hG)

/-- The outer-boundary-rooted annulus package canonically yields the attached-face peel
certificate used by the current boundary-aware Theorem 4.9 bridge. -/
noncomputable def
    attachedBoundaryRootedFacePeelCertificate_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb) :
    BoundaryRootedFacePeelCertificate emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) :=
  data.interiorData.toBoundaryRootedFacePeelCertificate

/-- The outer-boundary-rooted canonical parent package canonically yields the attached-face peel
certificate used by the current boundary-aware Theorem 4.9 bridge. -/
noncomputable def
    attachedBoundaryRootedFacePeelCertificate_of_planarBoundaryOuterBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryOuterBoundaryRootParentPeelData emb) :
    BoundaryRootedFacePeelCertificate emb.faces.attach
      (ambientFaceBoundary (allFaces := emb.faces) emb.faceBoundary) :=
  data.interiorData.toBoundaryRootedFacePeelCertificate

/-- Direct annulus-shaped annihilator theorem from the outer-boundary-rooted interior-dual Step 2
package. The proof route is unchanged; the extra conclusion is that the chosen roots were
localized on the distinguished outer boundary component. -/
theorem zero_on_allEdges_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ f ∈ data.interiorData.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
          data.interiorData.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.interiorData.roots
            data.interiorData.hcoverRoots data.interiorData.hsepRoots)
          data.interiorData.fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                data.interiorData.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.interiorData.roots
                  data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                data.interiorData.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                data.interiorData.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.interiorData.roots
                  data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                data.interiorData.fallbackEdge f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                data.interiorData.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.interiorData.roots
                  data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                data.interiorData.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                data.interiorData.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.interiorData.roots
                  data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                data.interiorData.fallbackEdge f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  exact zero_on_allEdges_of_planarBoundaryInteriorDualBoundaryRootAdjDistancePeelData
    (emb := emb) (C := C) (htait := htait) (z := z)
    (data := data.interiorData)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Direct annulus-shaped annihilator theorem from the outer-boundary-rooted canonical parent
package. -/
theorem zero_on_allEdges_of_planarBoundaryOuterBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G)
    (data : PlanarBoundaryOuterBoundaryRootParentPeelData emb)
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0)
    (horth : ∀ f ∈ data.interiorData.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
          data.interiorData.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.interiorData.roots
            data.interiorData.hcoverRoots data.interiorData.hsepRoots)
          data.interiorData.fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                data.interiorData.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.interiorData.roots
                  data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                data.interiorData.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                data.interiorData.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.interiorData.roots
                  data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                data.interiorData.fallbackEdge f) + γ)
              (emb.faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                data.interiorData.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.interiorData.roots
                  data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                data.interiorData.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                data.interiorData.hunique
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.interiorData.roots
                  data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                data.interiorData.fallbackEdge f) + γ)
              (emb.faceBoundary f.1)) = 0) :
    ∀ e, z e = 0 := by
  exact zero_on_allEdges_of_planarBoundaryInteriorDualBoundaryRootParentPeelData
    (emb := emb) (C := C) (htait := htait) (z := z)
    (data := data.interiorData)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Existential annulus-shaped global annihilator form of the outer-boundary-rooted Step 2
package. -/
theorem zero_on_allEdges_of_exists_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ f ∈ data.interiorData.peelFaces,
          ∀ γ, γ ≠ 0 → γ ≠ C
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
              data.interiorData.hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.interiorData.roots
                data.interiorData.hcoverRoots data.interiorData.hsepRoots)
              data.interiorData.fallbackEdge f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                    data.interiorData.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                      data.interiorData.roots
                      data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                    data.interiorData.fallbackEdge f))
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                    data.interiorData.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                      data.interiorData.roots
                      data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                    data.interiorData.fallbackEdge f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                    data.interiorData.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                      data.interiorData.roots
                      data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                    data.interiorData.fallbackEdge f))
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                    data.interiorData.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                      data.interiorData.roots
                      data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                    data.interiorData.fallbackEdge f) + γ)
                  (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Existential annulus-shaped global annihilator form of the outer-boundary-rooted canonical
parent package. -/
theorem zero_on_allEdges_of_exists_planarBoundaryOuterBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ data : PlanarBoundaryOuterBoundaryRootParentPeelData emb,
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ f ∈ data.interiorData.peelFaces,
          ∀ γ, γ ≠ 0 → γ ≠ C
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
              data.interiorData.hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.interiorData.roots
                data.interiorData.hcoverRoots data.interiorData.hsepRoots)
              data.interiorData.fallbackEdge f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                    data.interiorData.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                      data.interiorData.roots
                      data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                    data.interiorData.fallbackEdge f))
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                    data.interiorData.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                      data.interiorData.roots
                      data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                    data.interiorData.fallbackEdge f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                    data.interiorData.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                      data.interiorData.roots
                      data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                    data.interiorData.fallbackEdge f))
                  (C (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces
                    data.interiorData.hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                      data.interiorData.roots
                      data.interiorData.hcoverRoots data.interiorData.hsepRoots)
                    data.interiorData.fallbackEdge f) + γ)
                  (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, data, hzeroBoundary, horth⟩
  exact zero_on_allEdges_of_planarBoundaryOuterBoundaryRootParentPeelData
    (emb := emb) (C := C) (htait := htait) (z := z) (data := data)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

end Mettapedia.GraphTheory.FourColor
