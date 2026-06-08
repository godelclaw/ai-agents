import Mettapedia.GraphTheory.FourColor.PlanarBoundaryAnnulusConstructionCore

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Graph-level existence form of the BFS-stratified annulus construction target. -/
def AdmitsPlanarBoundaryAnnulusConstruction (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryAnnulusConstruction emb)

theorem admitsPlanarBoundaryAnnulusConstruction_of_admitsPlanarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionFaceLayerData G) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.construction⟩⟩

theorem
    admitsPlanarBoundaryAnnulusConstruction_of_admitsPlanarBoundaryAnnulusConstructionPositiveFrontierData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionPositiveFrontierData G) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.construction⟩⟩

theorem admitsPlanarBoundaryAnnulusConstruction_of_admitsPlanarBoundaryAnnulusConstructionFacePartitionData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionFacePartitionData G) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.construction⟩⟩

theorem
    admitsPlanarBoundaryAnnulusConstruction_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData G) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.construction⟩⟩

/-- Any graph admitting the BFS-stratified annulus construction also admits the current
theorem-layer finite collar witness package, by grouping faces by their face-distance strata on
the same embedding. -/
theorem admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstruction
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusConstruction G) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryCollarLayerFacePeelWitnessData⟩⟩

/-- Basic constructor: an annulus boundary split together with any boundary-aware height-ordered
face-peeling package yields a BFS-style annulus construction by reusing the given heights as face
distances. -/
def planarBoundaryAnnulusConstruction_of_boundaryData_and_heightOrderedFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb) :
    PlanarBoundaryAnnulusConstruction emb := by
  refine
    { toPlanarBoundaryAnnulusBoundaryData := boundaryData
      peelFaces := data.peelFaces
      witnessEdge := data.witnessEdge
      faceDistance := data.height
      hcover := data.hcover
      hwitness := data.hwitness
      hrest := ?_ }
  intro f hf e he
  rcases data.hrest f hf e he with hboundary | hdeeper
  · exact Or.inl <| by
      simpa [boundaryData.ambientBoundary_eq] using hboundary
  · exact Or.inr hdeeper

/-- Shared-endpoint boundary-component reachability data plus any boundary-aware height-ordered
face-peeling package already determines a BFS annulus construction, by first extracting the
ambient outer/inner boundary split from the reachability witness. -/
noncomputable def
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_heightOrderedFacePeelWitnessData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : PlanarBoundaryHeightOrderedFacePeelWitnessData emb) :
    PlanarBoundaryAnnulusConstruction emb :=
  planarBoundaryAnnulusConstruction_of_boundaryData_and_heightOrderedFacePeelWitnessData
    boundaryData.toPlanarBoundaryAnnulusBoundaryData data

/-- The corrected root-free interior-dual endpoint for the annulus route: shared-endpoint
boundary-component reachability together with explicit height-parent data already determines the
BFS annulus construction on the same embedding. This avoids the over-strong outer-root
localization package while still retaining the face-distance stratification needed downstream. -/
noncomputable def
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualHeightParentPeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryAnnulusConstruction emb :=
  planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_heightOrderedFacePeelWitnessData
    boundaryData
    (planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData data)

/-- The corrected root-free interior-dual height-parent route already supplies the exact
construction-side parent-witness orientation property on the same embedding. The witness edge used
by the annulus construction is the parent shared interior edge from the interior-dual package, and
the construction face distance is exactly the supplied strictly decreasing height. -/
theorem
    parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualHeightParentPeelData emb.faces emb.faceBoundary) :
    (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
      boundaryData data).ParentWitnessOrientation := by
  intro g hg
  rcases data.hparent g hg with ⟨p, hgp⟩
  refine ⟨p, ?_, ?_⟩
  · rw [show
        (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
          boundaryData data).witnessEdge g =
          parentSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
            data.parentFace data.fallbackEdge data.hparentAdj g by
          rfl]
    rw [parentSharedInteriorEdgeOfPairwiseUnique_eq_sharedInteriorEdgeOfAdjOfPairwiseUnique
      emb.faceBoundary emb.faces data.hunique data.parentFace data.fallbackEdge
      data.hparentAdj hgp]
    exact
      sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
        emb.faceBoundary emb.faces data.hunique
        (interiorDualSpanningForest_le emb.faceBoundary emb.faces <| data.hparentAdj hgp)
  · simpa [planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData,
      planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_heightOrderedFacePeelWitnessData,
      planarBoundaryAnnulusConstruction_of_boundaryData_and_heightOrderedFacePeelWitnessData,
      planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData] using
      data.hheight g hg p hgp

/-- Root-distance version of the boundary-root adjacency-distance annulus construction. Unlike the
shifted collar-indexing construction below, this one keeps the unshifted interior-dual distance to
the selected boundary root. It is the parent-oriented repair of the same source data: first-collar
peeled faces have distance `1`, not `0`. -/
noncomputable def
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryAnnulusConstruction emb :=
  planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_heightOrderedFacePeelWitnessData
    boundaryData
    (planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualBoundaryRootAdjDistancePeelData
      data)

theorem
    faceDistance_eq_rootDistance_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (f : AmbientFace emb.faces) :
    (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
      boundaryData data).faceDistance f =
      (interiorDualSpanningForest emb.faceBoundary emb.faces).dist f
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
          data.hcoverRoots data.hsepRoots f) := by
  rfl

theorem
    parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
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
  have hgroot : g ≠ rootFace g :=
    ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
      emb.faceBoundary emb.faces data.peelFaces data.roots
      data.hcoverRoots data.hsepRoots hdisj hg
  have hgreach := reachable_interiorDualSpanningForestRoot
    emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots g
  rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := g)
      hgreach hgroot with ⟨p, hgp, hadjgp, hdistgp⟩
  refine ⟨p, ?_, ?_⟩
  · rw [show
        (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
          boundaryData data).witnessEdge g =
          rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
            rootFace data.fallbackEdge g by
        rfl]
    unfold rootedSharedInteriorEdgeOfPairwiseUnique
    rw [parentSharedInteriorEdgeOfPairwiseUnique_eq_sharedInteriorEdgeOfAdjOfPairwiseUnique
      emb.faceBoundary emb.faces data.hunique
      (parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces) rootFace)
      data.fallbackEdge
      (by
        intro u v huv
        exact parentTowardsRoot_some_adj
          (interiorDualSpanningForest emb.faceBoundary emb.faces) rootFace huv)
      hgp]
    exact
      sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
        emb.faceBoundary emb.faces data.hunique
        (interiorDualSpanningForest_le emb.faceBoundary emb.faces hadjgp)
  · have hroot : rootFace p = rootFace g := by
      simpa [rootFace] using
        (interiorDualSpanningForestRoot_eq_of_adj
          emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots hadjgp).symm
    change T.dist p (rootFace p) < T.dist g (rootFace g)
    rw [hroot]
    omega

/-- The parent-oriented root-distance construction cannot be repackaged as the current
zero-based positive-frontier shell.  This records the exact bookkeeping mismatch: the
root-distance repair is the right construction for parent witnesses, but the existing
positive-frontier data structure still forces all strata, including stratum `0`, to be inhabited.
-/
theorem
    not_exists_planarBoundaryAnnulusConstructionPositiveFrontierData_with_rootDistanceConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    ¬ ∃ frontierData : PlanarBoundaryAnnulusConstructionPositiveFrontierData emb,
      frontierData.construction =
        planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
          boundaryData data := by
  let rootConstruction :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
      boundaryData data
  have horient : rootConstruction.ParentWitnessOrientation := by
    simpa [rootConstruction] using
      parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        boundaryData data
  rintro ⟨frontierData, hconstruction⟩
  have hnot : ¬ rootConstruction.ParentWitnessOrientation := by
    simpa [rootConstruction, hconstruction] using frontierData.not_parentWitnessOrientation
  exact hnot horient

/-- An explicit annulus decomposition together with witness-edge ownership data canonically
determines the BFS annulus construction layer, by passing through the already formalized local
remainder collar package and then regrouping faces by the induced layer height. This directly
reuses the older `Γ_t`-based geometry route rather than rebuilding the construction from scratch.
-/
noncomputable def planarBoundaryAnnulusConstruction_of_annulusWitnessAssignment
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (decomp : PlanarBoundaryAnnulusDecomposition emb)
    (data : PlanarBoundaryAnnulusWitnessAssignment decomp) :
    PlanarBoundaryAnnulusConstruction emb :=
  planarBoundaryAnnulusConstruction_of_boundaryData_and_heightOrderedFacePeelWitnessData
    decomp.toPlanarBoundaryAnnulusBoundaryData
    ((planarBoundaryCollarLayerFacePeelWitnessData_of_genericLocalRemainderBoundaryCollarLayerFacePeelWitnessData
      data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData).toHeightOrderedFacePeelWitnessData)

/-- The bundled annulus collar geometry also canonically lowers to the BFS annulus construction
layer on the same embedding. This is the direct bridge from an explicit collar decomposition with
witness ownership into the current construction file. -/
noncomputable def planarBoundaryAnnulusConstruction_of_annulusCollarGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusCollarGeometry emb) :
    PlanarBoundaryAnnulusConstruction emb :=
  planarBoundaryAnnulusConstruction_of_annulusWitnessAssignment
    data.toPlanarBoundaryAnnulusDecomposition data.toWitnessAssignment

theorem admitsPlanarBoundaryAnnulusConstruction_of_admitsPlanarBoundaryAnnulusWitnessAssignment
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusWitnessAssignment G) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, decomp, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryAnnulusConstruction_of_annulusWitnessAssignment decomp data⟩⟩

theorem admitsPlanarBoundaryAnnulusConstruction_of_admitsPlanarBoundaryAnnulusCollarGeometry
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryAnnulusCollarGeometry G) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryAnnulusConstruction_of_annulusCollarGeometry data⟩⟩

/-- Specialized constructor from the live boundary-root adjacency-distance interior-dual route.
This is the current direct path from root-distance data to the annulus construction layer.
Unlike the generic height-ordered witness-cover interface, the annulus collars should start at the
outermost peeled layer rather than at the boundary roots themselves. Since peeled faces are
disjoint from the boundary-root set, the correct annulus stratum index is therefore the interior-
dual root distance minus one. -/
noncomputable def
    planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryAnnulusConstruction emb := by
  let T := interiorDualSpanningForest emb.faceBoundary emb.faces
  let rootFace : AmbientFace emb.faces → AmbientFace emb.faces :=
    interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
      data.hcoverRoots data.hsepRoots
  let witnessEdge : AmbientFace emb.faces → G.edgeSet :=
    rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
      rootFace data.fallbackEdge
  let faceDistance : AmbientFace emb.faces → ℕ :=
    fun f => T.dist f (rootFace f) - 1
  have hdisj : Disjoint data.peelFaces data.roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      emb.faceBoundary emb.faces data.peelFaces data.roots
      data.hpeelInterior data.hrootsBoundary
  refine
    { toPlanarBoundaryAnnulusBoundaryData := boundaryData
      peelFaces := data.peelFaces
      witnessEdge := witnessEdge
      faceDistance := faceDistance
      hcover := ?_
      hwitness := ?_
      hrest := ?_ }
  · simpa [witnessEdge, rootFace] using data.hcover
  · intro f hf
    have hneq : f ≠ rootFace f :=
      ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
        emb.faceBoundary emb.faces data.peelFaces data.roots
        data.hcoverRoots data.hsepRoots hdisj hf
    rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := f)
        (h := reachable_interiorDualSpanningForestRoot
          emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots f)
        hneq with ⟨p, hfp, _hadj, _hdist⟩
    simpa [witnessEdge, rootFace] using
      rootedSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        emb.faceBoundary emb.faces data.hunique rootFace data.fallbackEdge hfp
  · intro f hf e he
    rcases data.hchildren f hf e he with hboundary | ⟨g, hg, hadj, heg, hlt⟩
    · exact Or.inl <| by
        simpa [boundaryData.ambientBoundary_eq] using hboundary
    · have hroot : rootFace f = rootFace g := by
        simpa [rootFace] using
          interiorDualSpanningForestRoot_eq_of_adj
            emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots hadj
      have hgf : parentTowardsRoot T rootFace g = some f := by
        exact parentTowardsRoot_eq_some_of_adj_of_lt_dist_of_componentConstantRoot
          T (interiorDualSpanningForest_isAcyclic emb.faceBoundary emb.faces)
          rootFace hadj
          (reachable_interiorDualSpanningForestRoot
            emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots f)
          (reachable_interiorDualSpanningForestRoot
            emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots g)
          hroot hlt
      have hfroot : f ≠ rootFace f :=
        ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
          emb.faceBoundary emb.faces data.peelFaces data.roots
          data.hcoverRoots data.hsepRoots hdisj hf
      have hgroot : g ≠ rootFace g :=
        ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
          emb.faceBoundary emb.faces data.peelFaces data.roots
          data.hcoverRoots data.hsepRoots hdisj hg
      have hfreach := reachable_interiorDualSpanningForestRoot
        emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots f
      have hgreach := reachable_interiorDualSpanningForestRoot
        emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots g
      have hfpos : 0 < T.dist f (rootFace f) := by
        apply Nat.pos_of_ne_zero
        intro hzero
        exact hfroot ((hfreach.dist_eq_zero_iff).1 hzero)
      have hgpos : 0 < T.dist g (rootFace g) := by
        apply Nat.pos_of_ne_zero
        intro hzero
        exact hgroot ((hgreach.dist_eq_zero_iff).1 hzero)
      have hdistg : T.dist f (rootFace f) + 1 = T.dist g (rootFace g) := by
        rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := g)
            hgreach hgroot with ⟨w, hw, _hadj, hdist⟩
        rw [hgf] at hw
        injection hw with hwf
        subst w
        simpa [hroot] using hdist
      have hfsub : T.dist f (rootFace f) - 1 + 1 = T.dist f (rootFace f) := by
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt hfpos)
      have hgsub : T.dist g (rootFace g) - 1 + 1 = T.dist g (rootFace g) := by
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt hgpos)
      refine Or.inr ⟨g, hg, ?_, ?_⟩
      · exact rootedSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
          emb.faceBoundary emb.faces data.hunique rootFace data.fallbackEdge
          data.hall hgf heg ((Finset.mem_erase.1 he).2)
      · dsimp [faceDistance]
        omega

/-- Shared-endpoint boundary-component reachability data plus the live interior-dual
adjacency-distance peel package determine a BFS annulus construction on the same embedding. This
is the current strongest purely constructive route that does not presuppose an abstract outer/inner
boundary split. -/
noncomputable def
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryAnnulusConstruction emb :=
  planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData.toPlanarBoundaryAnnulusBoundaryData data

theorem
    faceDistance_shifted_add_one_eq_rootDistance_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    {g : AmbientFace emb.faces} (hg : g ∈ data.peelFaces) :
    (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData data).faceDistance g + 1 =
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        boundaryData data).faceDistance g := by
  let T := interiorDualSpanningForest emb.faceBoundary emb.faces
  let rootFace : AmbientFace emb.faces → AmbientFace emb.faces :=
    interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
      data.hcoverRoots data.hsepRoots
  have hdisj : Disjoint data.peelFaces data.roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      emb.faceBoundary emb.faces data.peelFaces data.roots
      data.hpeelInterior data.hrootsBoundary
  have hgroot : g ≠ rootFace g :=
    ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
      emb.faceBoundary emb.faces data.peelFaces data.roots
      data.hcoverRoots data.hsepRoots hdisj hg
  have hgreach := reachable_interiorDualSpanningForestRoot
    emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots g
  have hpos : 0 < T.dist g (rootFace g) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hgroot ((hgreach.dist_eq_zero_iff).1 hzero)
  change T.dist g (rootFace g) - 1 + 1 = T.dist g (rootFace g)
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)

/-- The parent-oriented root-distance repair is exactly the one-step reindexing of the shifted
annulus construction on peeled faces: root-distance layer `n+1` is the shifted construction layer
`n`.  This is the concrete finite-set calibration behind the zero-stratum obstruction for the
current positive-frontier shell. -/
theorem
    rootDistance_faceDistance_succ_filter_eq_shifted_faceDistance_filter_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (n : ℕ) :
    data.peelFaces.filter (fun g =>
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        boundaryData data).faceDistance g = n + 1) =
    data.peelFaces.filter (fun g =>
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).faceDistance g = n) := by
  let shifted :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData data
  let root :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
      boundaryData data
  ext g
  constructor
  · intro hg
    rcases Finset.mem_filter.1 hg with ⟨hpeel, hroot⟩
    have hshiftRoot : shifted.faceDistance g + 1 = root.faceDistance g := by
      simpa [shifted, root] using
        faceDistance_shifted_add_one_eq_rootDistance_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData data hpeel
    have hsucc : shifted.faceDistance g + 1 = n + 1 := hshiftRoot.trans hroot
    have hshift : shifted.faceDistance g = n := Nat.add_right_cancel hsucc
    exact Finset.mem_filter.2 ⟨hpeel, hshift⟩
  · intro hg
    rcases Finset.mem_filter.1 hg with ⟨hpeel, hshift⟩
    have hshiftRoot : shifted.faceDistance g + 1 = root.faceDistance g := by
      simpa [shifted, root] using
        faceDistance_shifted_add_one_eq_rootDistance_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData data hpeel
    have hroot : root.faceDistance g = n + 1 := by
      rw [← hshiftRoot, hshift]
    exact Finset.mem_filter.2 ⟨hpeel, hroot⟩

/-- First-layer specialization of the root-distance/shifted-construction reindexing: the
root-distance faces at distance `1` are exactly the shifted construction's zero-distance peeled
faces. -/
theorem
    rootDistance_faceDistance_one_filter_eq_shifted_faceDistance_zero_filter_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    data.peelFaces.filter (fun g =>
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        boundaryData data).faceDistance g = 1) =
    data.peelFaces.filter (fun g =>
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).faceDistance g = 0) := by
  simpa using
    rootDistance_faceDistance_succ_filter_eq_shifted_faceDistance_filter_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData data 0

/-- On the shifted boundary-root adjacency-distance construction, the exact strict
`ParentWitnessOrientation` surface is equivalent to the absence of first-collar peeled faces:
every peeled face must have positive construction distance. Faces at distance zero cannot satisfy
strict parent orientation because the annulus construction already compresses root faces to the
same `0` stratum by subtracting one from the interior-dual root distance. -/
theorem
    parentWitnessOrientation_iff_pos_faceDistance_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData data).ParentWitnessOrientation ↔
      ∀ g ∈ data.peelFaces,
        0 < (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData data).faceDistance g := by
  constructor
  · intro horient g hg
    exact
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).faceDistance_pos_of_parentWitness horient hg
  · let T := interiorDualSpanningForest emb.faceBoundary emb.faces
    let rootFace : AmbientFace emb.faces → AmbientFace emb.faces :=
      interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
        data.hcoverRoots data.hsepRoots
    have hdisj : Disjoint data.peelFaces data.roots :=
      disjoint_peelFaces_roots_of_boundarySeparation
        emb.faceBoundary emb.faces data.peelFaces data.roots
        data.hpeelInterior data.hrootsBoundary
    intro hpos g hg
    have hgroot : g ≠ rootFace g :=
      ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
        emb.faceBoundary emb.faces data.peelFaces data.roots
        data.hcoverRoots data.hsepRoots hdisj hg
    have hgreach := reachable_interiorDualSpanningForestRoot
      emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots g
    rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := g)
        hgreach hgroot with ⟨p, hgp, hadjgp, hdistgp⟩
    have hroot : rootFace p = rootFace g := by
      simpa [rootFace] using
        (interiorDualSpanningForestRoot_eq_of_adj
          emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots hadjgp).symm
    refine ⟨p, ?_, ?_⟩
    · rw [show
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData data).witnessEdge g =
            rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces data.hunique
              rootFace data.fallbackEdge g by
            rfl]
      unfold rootedSharedInteriorEdgeOfPairwiseUnique
      rw [parentSharedInteriorEdgeOfPairwiseUnique_eq_sharedInteriorEdgeOfAdjOfPairwiseUnique
        emb.faceBoundary emb.faces data.hunique
        (parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces) rootFace)
        data.fallbackEdge
        (by
          intro u v huv
          exact parentTowardsRoot_some_adj
            (interiorDualSpanningForest emb.faceBoundary emb.faces) rootFace huv)
        hgp]
      exact
        sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
          emb.faceBoundary emb.faces data.hunique
          (interiorDualSpanningForest_le emb.faceBoundary emb.faces hadjgp)
    · have hposg :
          0 <
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData data).faceDistance g :=
        hpos g hg
      change T.dist p (rootFace p) - 1 < T.dist g (rootFace g) - 1
      change 0 < T.dist g (rootFace g) - 1 at hposg
      rw [hroot]
      omega

/-- The exact obstruction to strict parent-witness orientation for the shifted boundary-root
adjacency-distance construction is the presence of a first-collar peeled face. This keeps the
strengthened route honest: the original shifted construction only reaches the parent-oriented
surface after the zero-distance peeled faces have been excluded. -/
theorem
    not_parentWitnessOrientation_iff_exists_zero_faceDistance_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    ¬ (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).ParentWitnessOrientation ↔
      ∃ g ∈ data.peelFaces,
        (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData data).faceDistance g = 0 := by
  classical
  let c :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData data
  have horient_iff :
      c.ParentWitnessOrientation ↔ ∀ g ∈ data.peelFaces, 0 < c.faceDistance g := by
    simpa [c] using
      parentWitnessOrientation_iff_pos_faceDistance_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data
  constructor
  · intro hnot
    by_contra hzero
    apply hnot
    exact horient_iff.2 (by
      intro g hg
      apply Nat.pos_of_ne_zero
      intro hgzero
      exact hzero ⟨g, hg, hgzero⟩)
  · rintro ⟨g, hg, hgzero⟩ horient
    have hpos : 0 < c.faceDistance g := horient_iff.1 horient g hg
    have hgzero' : c.faceDistance g = 0 := by
      simpa [c] using hgzero
    rw [hgzero'] at hpos
    exact (Nat.not_lt_zero 0 hpos).elim

/-- The first positive root-distance layer is exactly the obstruction layer for the shifted annulus
construction: it is nonempty precisely when the shifted construction fails strict parent-witness
orientation. -/
theorem
    rootDistance_faceDistance_one_filter_nonempty_iff_not_shifted_parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    (data.peelFaces.filter (fun g =>
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        boundaryData data).faceDistance g = 1)).Nonempty ↔
      ¬ (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).ParentWitnessOrientation := by
  let shifted :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData data
  let root :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
      boundaryData data
  change (data.peelFaces.filter (fun g => root.faceDistance g = 1)).Nonempty ↔
    ¬ shifted.ParentWitnessOrientation
  have hlayer :
      data.peelFaces.filter (fun g => root.faceDistance g = 1) =
        data.peelFaces.filter (fun g => shifted.faceDistance g = 0) := by
    simpa [shifted, root] using
      rootDistance_faceDistance_one_filter_eq_shifted_faceDistance_zero_filter_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data
  have hnot :
      ¬ shifted.ParentWitnessOrientation ↔
        ∃ g ∈ data.peelFaces, shifted.faceDistance g = 0 := by
    simpa [shifted] using
      not_parentWitnessOrientation_iff_exists_zero_faceDistance_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data
  constructor
  · rintro ⟨g, hgroot⟩
    have hgshift : g ∈ data.peelFaces.filter (fun g => shifted.faceDistance g = 0) := by
      simpa [hlayer] using hgroot
    rcases Finset.mem_filter.1 hgshift with ⟨hpeel, hzero⟩
    exact hnot.2 ⟨g, hpeel, hzero⟩
  · intro hfail
    rcases hnot.1 hfail with ⟨g, hpeel, hzero⟩
    refine ⟨g, ?_⟩
    have hgshift : g ∈ data.peelFaces.filter (fun g => shifted.faceDistance g = 0) :=
      Finset.mem_filter.2 ⟨hpeel, hzero⟩
    simpa [hlayer] using hgshift

/-- Exact strengthened continuation theorem on the shifted boundary-root adjacency-distance route:
once every peeled face has positive annulus construction distance, the same-embedding data reaches
the honest parent-witness orientation surface. -/
theorem
    parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_pos_faceDistance
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hpos : ∀ g ∈ data.peelFaces,
      0 <
        (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData data).faceDistance g) :
    (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData data).ParentWitnessOrientation :=
  (parentWitnessOrientation_iff_pos_faceDistance_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData data).2 hpos

/-- Structural reformulation of the exact strengthened shifted boundary-root adjacency-distance
condition: strict parent-witness orientation is equivalent to saying that the canonical
`parentTowardsRoot` predecessor of every peeled face is itself peeled. This expresses the
first-collar exclusion directly on the original interior-dual source object rather than through the
derived shifted annulus distance. -/
theorem
    parentWitnessOrientation_iff_exists_parent_mem_peelFaces_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData data).ParentWitnessOrientation ↔
      ∀ g ∈ data.peelFaces,
        ∃ p ∈ data.peelFaces,
          parentTowardsRoot
              (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
                data.hcoverRoots data.hsepRoots)
              g = some p := by
  let c :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData data
  let T := interiorDualSpanningForest emb.faceBoundary emb.faces
  let rootFace : AmbientFace emb.faces → AmbientFace emb.faces :=
    interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
      data.hcoverRoots data.hsepRoots
  have hdisj : Disjoint data.peelFaces data.roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      emb.faceBoundary emb.faces data.peelFaces data.roots
      data.hpeelInterior data.hrootsBoundary
  change c.ParentWitnessOrientation ↔
    ∀ g ∈ data.peelFaces, ∃ p ∈ data.peelFaces, parentTowardsRoot T rootFace g = some p
  constructor
  · intro horient g hg
    have hposg : 0 < c.faceDistance g := c.faceDistance_pos_of_parentWitness horient hg
    have hgroot : g ≠ rootFace g :=
      ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
        emb.faceBoundary emb.faces data.peelFaces data.roots
        data.hcoverRoots data.hsepRoots hdisj hg
    have hgreach := reachable_interiorDualSpanningForestRoot
      emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots g
    rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := g)
        hgreach hgroot with ⟨p, hgp, hadjgp, hdistgp⟩
    refine ⟨p, ?_, hgp⟩
    by_contra hpPeel
    have hpRoot : p ∈ data.roots :=
      data.mem_roots_of_not_mem_peelFaces hpPeel
    have hpSelf : rootFace p = p := by
      unfold rootFace interiorDualSpanningForestRoot
      let hrootsT :=
        hasUniqueReachableRoot_of_cover_and_separated T data.roots
          ((rootSetCovers_congr_reachable data.roots
            (interiorDualSpanningForest_reachable_eq emb.faceBoundary emb.faces)).2
            data.hcoverRoots)
          ((rootSetSeparated_congr_reachable data.roots
            (interiorDualSpanningForest_reachable_eq emb.faceBoundary emb.faces)).2
            data.hsepRoots)
      change uniqueReachableRoot T data.roots hrootsT p = p
      apply (hrootsT p).unique
      · exact ⟨uniqueReachableRoot_mem_roots T data.roots hrootsT p,
          reachable_uniqueReachableRoot T data.roots hrootsT p⟩
      · exact ⟨hpRoot, SimpleGraph.Reachable.refl (G := T) p⟩
    have hroot : rootFace g = rootFace p := by
      simpa [rootFace] using
        interiorDualSpanningForestRoot_eq_of_adj
          emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots hadjgp
    have hrootgp : rootFace g = p := by
      calc
        rootFace g = rootFace p := hroot
        _ = p := hpSelf
    have hdistone : T.dist g (rootFace g) = 1 := by
      simpa [hrootgp] using hdistgp.symm
    change 0 < T.dist g (rootFace g) - 1 at hposg
    omega
  · intro hparent
    apply
      parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_pos_faceDistance
      boundaryData data
    intro g hg
    rcases hparent g hg with ⟨p, hp, hgp⟩
    have hgroot : g ≠ rootFace g :=
      ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
        emb.faceBoundary emb.faces data.peelFaces data.roots
        data.hcoverRoots data.hsepRoots hdisj hg
    have hgreach := reachable_interiorDualSpanningForestRoot
      emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots g
    rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := g)
        hgreach hgroot with ⟨w, hw, _hadj, hdist⟩
    rw [hgp] at hw
    injection hw with hwp
    subst w
    have hadjgp : T.Adj g p :=
      parentTowardsRoot_some_adj T rootFace hgp
    have hroot : rootFace g = rootFace p := by
      simpa [rootFace] using
        interiorDualSpanningForestRoot_eq_of_adj
          emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots hadjgp
    have hpneq : p ≠ rootFace g := by
      have hpneq' : p ≠ rootFace p :=
        ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
          emb.faceBoundary emb.faces data.peelFaces data.roots
          data.hcoverRoots data.hsepRoots hdisj hp
      intro hEq
      apply hpneq'
      simpa [hEq] using hroot
    have hpreach0 := reachable_interiorDualSpanningForestRoot
      emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots p
    have hpreach : T.Reachable p (rootFace g) := by
      simpa [hroot] using hpreach0
    have hppos : 0 < T.dist p (rootFace g) := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hpneq ((hpreach.dist_eq_zero_iff).1 hz)
    have hdistgp : T.dist p (rootFace g) + 1 = T.dist g (rootFace g) := by
      simpa using hdist
    change 0 < T.dist g (rootFace g) - 1
    omega

/-- On the shifted boundary-root adjacency-distance route, the structural peeled-parent condition
is equivalent to positive annulus construction distance on every peeled face. This removes the
intermediate `ParentWitnessOrientation` layer from the exact source-side repair statement. -/
theorem
    exists_parent_mem_peelFaces_iff_pos_faceDistance_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    (∀ g ∈ data.peelFaces,
      ∃ p ∈ data.peelFaces,
        parentTowardsRoot
            (interiorDualSpanningForest emb.faceBoundary emb.faces)
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces data.roots
              data.hcoverRoots data.hsepRoots)
            g = some p) ↔
      ∀ g ∈ data.peelFaces,
        0 <
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData data).faceDistance g := by
  constructor
  · intro hparent
    have horient :
        (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData data).ParentWitnessOrientation :=
      (parentWitnessOrientation_iff_exists_parent_mem_peelFaces_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).2 hparent
    exact
      (parentWitnessOrientation_iff_pos_faceDistance_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).1 horient
  · intro hpos
    have horient :
        (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
          boundaryData data).ParentWitnessOrientation :=
      (parentWitnessOrientation_iff_pos_faceDistance_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).2 hpos
    exact
      (parentWitnessOrientation_iff_exists_parent_mem_peelFaces_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).1 horient

theorem
    outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_boundaryComponentConstant
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hconst : ∀ f : AmbientFace emb.faces,
      boundaryData.BoundaryComponentConstantOnFace f) :
    Disjoint
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).outerBoundaryFaces
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).innerBoundaryFaces := by
  simpa [PlanarBoundaryAnnulusConstruction.outerBoundaryFaces,
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces,
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
    using
      boundaryData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentConstant
        hconst

theorem
    outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_boundaryComponentReachable
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hreach : ∀ f : AmbientFace emb.faces,
      BoundaryComponentReachableOnFace (emb := emb) f) :
    Disjoint
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).outerBoundaryFaces
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).innerBoundaryFaces := by
  simpa [PlanarBoundaryAnnulusConstruction.outerBoundaryFaces,
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces,
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
    using
      boundaryData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentReachable
        hreach

theorem
    outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_boundaryEdgesShareEndpoint
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hshare : ∀ f : AmbientFace emb.faces,
      BoundaryEdgesShareEndpointOnFace (emb := emb) f) :
    Disjoint
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).outerBoundaryFaces
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).innerBoundaryFaces := by
  simpa [PlanarBoundaryAnnulusConstruction.outerBoundaryFaces,
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces,
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
    using
      boundaryData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryEdgesShareEndpoint
        hshare

theorem
    outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_boundaryComponentWalkOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hwalk : ∀ f : AmbientFace emb.faces,
      BoundaryComponentWalkOnFace (emb := emb) f) :
    Disjoint
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).outerBoundaryFaces
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).innerBoundaryFaces := by
  simpa [PlanarBoundaryAnnulusConstruction.outerBoundaryFaces,
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces,
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
    using
      boundaryData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentWalkOnFace
        hwalk

theorem
    outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_boundaryComponentRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hrun : ∀ f : AmbientFace emb.faces,
      BoundaryComponentRunOnFace (emb := emb) f) :
    Disjoint
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).outerBoundaryFaces
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).innerBoundaryFaces := by
  simpa [PlanarBoundaryAnnulusConstruction.outerBoundaryFaces,
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces,
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
    using
      boundaryData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryComponentRunOnFace
        hrun

theorem
    outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_boundarySelectedBoundaryRunOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hrun : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryRunOnFace (emb := emb) f) :
    Disjoint
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).outerBoundaryFaces
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).innerBoundaryFaces := by
  simpa [PlanarBoundaryAnnulusConstruction.outerBoundaryFaces,
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces,
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
    using
      PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundarySelectedBoundaryRunOnFace
        boundaryData hrun

theorem
    outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_boundarySelectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (harc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f) :
    Disjoint
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).outerBoundaryFaces
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).innerBoundaryFaces := by
  simpa [PlanarBoundaryAnnulusConstruction.outerBoundaryFaces,
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces,
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
    using
      PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundarySelectedBoundaryArcOnFace
        boundaryData harc

theorem
    outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_selectedBoundaryArcGeometry
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (geom : PlanarBoundarySelectedBoundaryArcGeometry emb) :
    Disjoint
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).outerBoundaryFaces
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).innerBoundaryFaces := by
  simpa [PlanarBoundaryAnnulusConstruction.outerBoundaryFaces,
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces,
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
    using
      PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_selectedBoundaryArcGeometry
        boundaryData geom

theorem
    outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_faceBoundaryRunGeometry_and_selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (geom : PlanarBoundaryFaceBoundaryRunGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces, geom.SelectedBoundaryArcOnFace f) :
    Disjoint
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).outerBoundaryFaces
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).innerBoundaryFaces := by
  simpa [PlanarBoundaryAnnulusConstruction.outerBoundaryFaces,
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces,
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
    using
      PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_faceBoundaryRunGeometry_and_selectedBoundaryArcOnFace
        boundaryData geom harc

theorem
    outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_orderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (geom : PlanarBoundaryOrderedFaceArcEmbeddingData emb) :
    Disjoint
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).outerBoundaryFaces
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).innerBoundaryFaces := by
  simpa [PlanarBoundaryAnnulusConstruction.outerBoundaryFaces,
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces,
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
    using
      PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_orderedFaceArcEmbeddingData
        boundaryData geom

theorem
    outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (geom : PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) :
    Disjoint
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).outerBoundaryFaces
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).innerBoundaryFaces := by
  simpa [PlanarBoundaryAnnulusConstruction.outerBoundaryFaces,
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces,
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
    using
      PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_cyclicOrderedFaceArcEmbeddingData
        boundaryData geom

theorem
    outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (geom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb)
    (harc : ∀ f : AmbientFace emb.faces,
      (geom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) :
    Disjoint
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).outerBoundaryFaces
      (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData data).innerBoundaryFaces := by
  simpa [PlanarBoundaryAnnulusConstruction.outerBoundaryFaces,
    PlanarBoundaryAnnulusConstruction.innerBoundaryFaces,
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
    using
      PlanarBoundaryAnnulusBoundaryReachabilityData.outerBoundaryFaces_disjoint_innerBoundaryFaces_of_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace
        boundaryData geom harc

/-- Specialized construction-side lowering from the concrete shared-endpoint boundary-component
route to the face-partition package. Relative to the older selected-boundary-contact shell, this
keeps only the genuinely needed cover/disjointness data on ambient outer-boundary faces, peeled
faces, and ambient inner-boundary faces. -/
noncomputable def
    planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryReachable : ∀ f : AmbientFace emb.faces,
      BoundaryComponentReachableOnFace (emb := emb) f)
    (hfaceCover :
      emb.faces.attach ⊆
        (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).outerBoundaryFaces ∪
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).peelFaces ∪
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).innerBoundaryFaces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionFacePartitionData emb := by
  let c :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData
  refine
    { construction := c
      hpeelInterior := ?_
      hfaceCover := ?_
      hboundaryFaceDisjoint := ?_
      hcurrentOuterBoundaryNonempty := ?_
      hcurrentOuterBoundaryDisjoint := ?_ }
  · intro f hf
    simpa [c,
      planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData,
      planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData]
      using interiorData.hpeelInterior f hf
  · simpa [c] using hfaceCover
  · simpa [c] using
      outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_boundaryComponentReachable
        boundaryData interiorData hboundaryReachable
  · intro i hi
    simpa [c] using hcurrentOuterBoundaryNonempty i hi
  · intro i j hi hj hij
    simpa [c] using hcurrentOuterBoundaryDisjoint (i := i) (j := j) hi hj hij

/-- The same face-partition shell can be driven directly by the stronger ordered embedding-side
face-boundary interface. This removes the unnecessary selected-boundary-contact hypothesis while
retaining the same positive current-frontier obligations. -/
noncomputable def
    planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundaryOrderedFaceArcEmbeddingData emb)
    (hfaceCover :
      emb.faces.attach ⊆
        (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).outerBoundaryFaces ∪
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).peelFaces ∪
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).innerBoundaryFaces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionFacePartitionData emb :=
  planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryGeom.boundaryComponentReachableOnFace
    hfaceCover hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same face-partition shell can also be driven directly from the cyclic strengthening of the
ordered embedding-side face-boundary interface. -/
noncomputable def
    planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb)
    (hfaceCover :
      emb.faces.attach ⊆
        (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).outerBoundaryFaces ∪
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).peelFaces ∪
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).innerBoundaryFaces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionFacePartitionData emb :=
  planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryGeom.toPlanarBoundaryOrderedFaceArcEmbeddingData
    hfaceCover hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same face-partition shell can also be driven from the cyclic alternating edge/vertex
face-boundary walk layer, together with per-face selected-boundary contiguity on the induced
linear face-boundary runs. -/
noncomputable def
    planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hfaceCover :
      emb.faces.attach ⊆
        (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).outerBoundaryFaces ∪
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).peelFaces ∪
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).innerBoundaryFaces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionFacePartitionData emb :=
  planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData
    ((boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).boundaryComponentReachableOnFace
      hboundaryArc)
    hfaceCover hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same face-partition shell can also be driven from the honest facial closed-walk source
layer, together with per-face selected-boundary contiguity on the induced linear runs. -/
noncomputable def
    planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hfaceCover :
      emb.faces.attach ⊆
        (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).outerBoundaryFaces ∪
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).peelFaces ∪
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).innerBoundaryFaces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionFacePartitionData emb :=
  planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryGeom.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry
    (by
      intro f
      simpa
        [PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry,
          PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry,
          PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicOrderedFaceEmbeddingData,
          PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryFaceBoundaryRunGeometry]
        using hboundaryArc f)
    hfaceCover hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- Specialized construction-side lowering from the concrete shared-endpoint boundary-component
route to the selected-boundary face package. Relative to the older constructor shell, the ambient
outer/inner boundary-face disjointness is derived from facewise reachability in the primal
boundary graph instead of being assumed as a separate finite-set hypothesis. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryReachable : ∀ f : AmbientFace emb.faces,
      BoundaryComponentReachableOnFace (emb := emb) f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb := by
  let c :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData
  refine
    { construction := c
      hpeelInterior := ?_
      hnonPeelSelectedBoundary := ?_
      hboundaryFaceDisjoint := ?_
      hcurrentOuterBoundaryNonempty := ?_
      hcurrentOuterBoundaryDisjoint := ?_ }
  · intro f hf
    simpa [c,
      planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData,
      planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData]
      using interiorData.hpeelInterior f hf
  · intro f hf
    simpa [c] using hnonPeelSelectedBoundary f hf
  · simpa [c] using
      outerBoundaryFaces_disjoint_innerBoundaryFaces_of_boundaryReachabilityData_and_boundaryComponentReachable
        boundaryData interiorData hboundaryReachable
  · intro i hi
    simpa [c] using hcurrentOuterBoundaryNonempty i hi
  · intro i j hi hj hij
    simpa [c] using hcurrentOuterBoundaryDisjoint (i := i) (j := j) hi hj hij

/-- On the live boundary-root adjacency-distance source object, non-peeled faces are already
boundary-root faces. Therefore the selected-boundary contact needed by the annulus construction
face shell is not an extra geometric hypothesis on this route. -/
theorem
    nonPeelSelectedBoundary_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  intro f hf
  have hf' : f ∉ interiorData.peelFaces := by
    simpa [planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData,
      planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData]
      using hf
  exact interiorData.exists_mem_selectedBoundarySupport_of_not_mem_peelFaces hf'

/-- Strengthened construction-side lowering from boundary-component reachability plus the live
boundary-root adjacency-distance package. The non-peeled selected-boundary contact is derived from
the interior-dual root data, so the only remaining face-side geometric input is reachability of the
selected boundary edges on each face. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundaryComponentReachableOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryReachable : ∀ f : AmbientFace emb.faces,
      BoundaryComponentReachableOnFace (emb := emb) f)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData hboundaryReachable
    (nonPeelSelectedBoundary_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData)
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same strengthened source surface reaches the finite face-partition shell without a
separate face-cover assumption: non-peeled selected-boundary contact is already supplied by the
interior-dual root data, and the outer/inner split comes from boundary reachability. -/
noncomputable def
    planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_boundaryComponentReachableOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryReachable : ∀ f : AmbientFace emb.faces,
      BoundaryComponentReachableOnFace (emb := emb) f)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionFacePartitionData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundaryComponentReachableOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData hboundaryReachable
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toFacePartitionData

/-- The strengthened source surface also reaches the positive-frontier shell directly, with the
non-peeled selected-boundary contact and face cover discharged by the interior-dual root data. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_boundaryComponentReachableOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryReachable : ∀ f : AmbientFace emb.faces,
      BoundaryComponentReachableOnFace (emb := emb) f)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundaryComponentReachableOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData hboundaryReachable
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- The same specialized shared-endpoint boundary-component route also lowers directly to the
older positive-frontier shell once facewise boundary reachability, non-peeled selected-boundary
contact, and the positive current-frontier facts are available. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryReachable : ∀ f : AmbientFace emb.faces,
      BoundaryComponentReachableOnFace (emb := emb) f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData hboundaryReachable hnonPeelSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- The same construction-side lowering can be driven by the strictly more local facewise
endpoint-sharing condition: selected-boundary edges on one ambient face merely have to share a
primal endpoint, rather than come equipped with a separate reachability proof in the boundary
component graph. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundaryEdgesShareEndpoint_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryShare : ∀ f : AmbientFace emb.faces,
      BoundaryEdgesShareEndpointOnFace (emb := emb) f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData
    (fun f =>
      boundaryComponentReachableOnFace_of_boundaryEdgesShareEndpointOnFace
        (hboundaryShare f))
    hnonPeelSelectedBoundary hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same construction-side lowering can be driven by the weaker face-supported walk witness in
the shared-endpoint boundary graph. This keeps the construction layer compatible with future raw
geometry that produces local boundary runs rather than immediate pairwise endpoint-sharing. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundaryComponentWalkOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryWalk : ∀ f : AmbientFace emb.faces,
      BoundaryComponentWalkOnFace (emb := emb) f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData
    (fun f =>
      boundaryComponentReachableOnFace_of_boundaryComponentWalkOnFace
        (hboundaryWalk f))
    hnonPeelSelectedBoundary hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same construction-side lowering can be driven by a pairwise ordered face-local boundary
run witness. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundaryComponentRunOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryRun : ∀ f : AmbientFace emb.faces,
      BoundaryComponentRunOnFace (emb := emb) f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData
    (fun f =>
      boundaryComponentReachableOnFace_of_boundaryComponentRunOnFace
        (hboundaryRun f))
    hnonPeelSelectedBoundary hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same construction-side lowering can be driven by one ordered list of all selected-boundary
edges on each ambient face. This is closer to actual face-boundary geometry than the pairwise run
shell, while still avoiding any extra cyclic-order structure on the embedding itself. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundarySelectedBoundaryRunOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryRun : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryRunOnFace (emb := emb) f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData
    (fun f =>
      boundaryComponentReachableOnFace_of_boundarySelectedBoundaryRunOnFace
        (hboundaryRun f))
    hnonPeelSelectedBoundary hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same construction-side lowering can be driven by a full ordered face-boundary run together
with the fact that the selected-boundary edges form one contiguous arc on that run. This is the
current closest local same-embedding shell to raw planar face-boundary geometry. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundarySelectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData
    (fun f =>
      boundaryComponentReachableOnFace_of_boundarySelectedBoundaryArcOnFace
        (hboundaryArc f))
    hnonPeelSelectedBoundary hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same construction-side lowering can be driven by a bundled embedding-side face-boundary
order together with one contiguous selected-boundary arc on each ambient face. This is the current
closest geometry-facing package to the paper's local face-boundary run language. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_selectedBoundaryArcGeometry_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundarySelectedBoundaryArcGeometry emb)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData
    boundaryGeom.boundaryComponentReachableOnFace
    hnonPeelSelectedBoundary hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same construction-side lowering can be driven by the two raw face-boundary geometry pieces
separately: one ordered full boundary run per face, and a proof that selected-boundary edges form
one contiguous block on that run. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_faceBoundaryRunGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryRunGeom : PlanarBoundaryFaceBoundaryRunGeometry emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      boundaryRunGeom.SelectedBoundaryArcOnFace f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData
    (boundaryRunGeom.boundaryComponentReachableOnFace hboundaryArc)
    hnonPeelSelectedBoundary hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same construction-side lowering can be driven directly by the stronger ordered
embedding-side face-boundary interface: one endpoint-sharing order per ambient face together with
one contiguous selected-boundary arc on that order. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundaryOrderedFaceArcEmbeddingData emb)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryGeom.boundaryComponentReachableOnFace
    hnonPeelSelectedBoundary hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same construction-side lowering can also be driven directly from the cyclic strengthening
of the ordered embedding-side face-boundary interface. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryGeom.toPlanarBoundaryOrderedFaceArcEmbeddingData
    hnonPeelSelectedBoundary hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same construction-side lowering can also be driven from the cyclic alternating
edge/vertex face-boundary walk layer, together with a separate proof that the selected-boundary
edges form one contiguous arc on each induced linear face-boundary run. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_faceBoundaryRunGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry
    hboundaryArc hnonPeelSelectedBoundary hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same construction-side lowering can also be driven from the honest facial closed-walk
source layer, together with a separate proof that the selected-boundary edges form one contiguous
arc on each induced linear face-boundary run. This keeps the walk-anchored source visible at the
construction endpoint instead of routing only through cyclic surrogate shells. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb :=
  planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryGeom.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry
    (by
      intro f
      simpa
        [PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry,
          PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryFaceBoundaryRunGeometry,
          PlanarBoundaryClosedWalkEmbeddingData.toPlanarBoundaryCyclicOrderedFaceEmbeddingData,
          PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry.toPlanarBoundaryFaceBoundaryRunGeometry]
        using hboundaryArc f)
    hnonPeelSelectedBoundary hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- The same positive-frontier shell can also be reached from the more local facewise
endpoint-sharing condition. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_boundaryEdgesShareEndpoint_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryShare : ∀ f : AmbientFace emb.faces,
      BoundaryEdgesShareEndpointOnFace (emb := emb) f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundaryEdgesShareEndpoint_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData hboundaryShare hnonPeelSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- The same positive-frontier shell can also be reached from the weaker face-supported walk
witness in the shared-endpoint boundary graph. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_boundaryComponentWalkOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryWalk : ∀ f : AmbientFace emb.faces,
      BoundaryComponentWalkOnFace (emb := emb) f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundaryComponentWalkOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData hboundaryWalk hnonPeelSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- The same positive-frontier shell can also be reached from the ordered face-local boundary-run
witness. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_boundaryComponentRunOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryRun : ∀ f : AmbientFace emb.faces,
      BoundaryComponentRunOnFace (emb := emb) f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundaryComponentRunOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData hboundaryRun hnonPeelSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- The same positive-frontier shell can also be reached from one ordered selected-boundary run on
each ambient face. This is the current closest same-embedding interface to genuine cyclic
face-boundary geometry. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_boundarySelectedBoundaryRunOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryRun : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryRunOnFace (emb := emb) f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundarySelectedBoundaryRunOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData hboundaryRun hnonPeelSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- The same positive-frontier shell can also be reached from a face-boundary order together with
the statement that selected-boundary edges form a single contiguous arc on that order. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_boundarySelectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      BoundarySelectedBoundaryArcOnFace (emb := emb) f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundarySelectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData hboundaryArc hnonPeelSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- The same positive-frontier shell can also be reached from the bundled embedding-side
face-boundary arc geometry witness. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_selectedBoundaryArcGeometry_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundarySelectedBoundaryArcGeometry emb)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_selectedBoundaryArcGeometry_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryGeom hnonPeelSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- The same positive-frontier shell can also be reached from the split raw face-boundary geometry
interface: ordered full face-boundary runs plus a separate selected-boundary contiguity proof. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_faceBoundaryRunGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryRunGeom : PlanarBoundaryFaceBoundaryRunGeometry emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      boundaryRunGeom.SelectedBoundaryArcOnFace f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_faceBoundaryRunGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryRunGeom hboundaryArc hnonPeelSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- The same positive-frontier shell can also be reached directly from the stronger ordered
embedding-side face-boundary interface. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundaryOrderedFaceArcEmbeddingData emb)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryGeom hnonPeelSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- The same positive-frontier shell can also be reached directly from the cyclic strengthening
of the ordered embedding-side face-boundary interface. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryGeom hnonPeelSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- The same positive-frontier shell can also be reached from the cyclic alternating edge/vertex
face-boundary walk layer plus per-face selected-boundary contiguity on the induced linear runs. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryGeom hboundaryArc hnonPeelSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- The same positive-frontier shell can also be reached from the honest facial closed-walk
source layer plus per-face selected-boundary contiguity on the induced linear runs. -/
noncomputable def
    planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hnonPeelSelectedBoundary : ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
            boundaryData interiorData).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionPositiveFrontierData emb :=
  (planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    boundaryData interiorData boundaryGeom hboundaryArc hnonPeelSelectedBoundary
    hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint).toPositiveFrontierData

/-- Graph-level lowering from concrete boundary-component reachability plus live interior-dual
adjacency-distance peel data to the selected-boundary-contact shell. The selected-boundary contact
for non-peeled faces is derived from the boundary-root condition inside the interior-dual package,
so it is not part of this theorem's input. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_boundaryComponentReachableOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces, BoundaryComponentReachableOnFace (emb := emb) f) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, hboundaryReachable,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_boundaryComponentReachableOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData hboundaryReachable
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering to the finite face-partition shell on the same strengthened source
surface. This removes the separate finite face-cover hypothesis from this interior-dual route. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionFacePartitionData_of_exists_boundaryReachabilityData_and_boundaryComponentReachableOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces, BoundaryComponentReachableOnFace (emb := emb) f) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionFacePartitionData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, hboundaryReachable,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_boundaryComponentReachableOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData hboundaryReachable
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering to the positive-frontier shell on the same strengthened source surface.
Only the positive current-frontier facts remain as frontier-specific inputs. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_boundaryReachabilityData_and_boundaryComponentReachableOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
        (∀ f : AmbientFace emb.faces, BoundaryComponentReachableOnFace (emb := emb) f) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionPositiveFrontierData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, hboundaryReachable,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_boundaryComponentReachableOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData hboundaryReachable
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering from the same-embedding ordered face-arc boundary geometry route plus
live interior-dual adjacency-distance peel data to the face-partition shell on the annulus
construction side. This weakens the remaining geometric obligation from per-face selected-
boundary contact to a direct finite-set face cover. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionFacePartitionData_of_exists_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      Nonempty (PlanarBoundaryOrderedFaceArcEmbeddingData emb) ∧
        (emb.faces.attach ⊆
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).outerBoundaryFaces ∪
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces ∪
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).innerBoundaryFaces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionFacePartitionData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, ⟨boundaryGeom⟩, hfaceCover,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData boundaryGeom hfaceCover
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering from the same-embedding cyclic ordered face-arc boundary geometry route
plus live interior-dual adjacency-distance peel data to the face-partition shell on the annulus
construction side. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionFacePartitionData_of_exists_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
        (emb.faces.attach ⊆
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).outerBoundaryFaces ∪
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces ∪
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).innerBoundaryFaces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionFacePartitionData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, ⟨boundaryGeom⟩, hfaceCover,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData boundaryGeom hfaceCover
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering from the same-embedding cyclic alternating edge/vertex face-boundary
walk layer plus per-face selected-boundary contiguity to the face-partition shell on the annulus
construction side. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionFacePartitionData_of_exists_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (emb.faces.attach ⊆
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).outerBoundaryFaces ∪
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces ∪
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).innerBoundaryFaces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionFacePartitionData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, boundaryGeom, hboundaryArc, hfaceCover,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData boundaryGeom hboundaryArc hfaceCover
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering from the honest facial closed-walk source layer plus per-face
selected-boundary contiguity to the face-partition shell on the annulus construction side. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionFacePartitionData_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (emb.faces.attach ⊆
          (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).outerBoundaryFaces ∪
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces ∪
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).innerBoundaryFaces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionFacePartitionData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, boundaryGeom, hboundaryArc, hfaceCover,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionFacePartitionData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData boundaryGeom hboundaryArc hfaceCover
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering from the same-embedding ordered face-arc boundary geometry route plus
live interior-dual adjacency-distance peel data to the selected-boundary-contact shell on the
annulus construction side. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      Nonempty (PlanarBoundaryOrderedFaceArcEmbeddingData emb) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, ⟨boundaryGeom⟩,
      hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
      hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData boundaryGeom hnonPeelSelectedBoundary
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering from the same-embedding cyclic ordered face-arc boundary geometry route
plus live interior-dual adjacency-distance peel data to the selected-boundary-contact shell on the
annulus construction side. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, ⟨boundaryGeom⟩,
      hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
      hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData boundaryGeom hnonPeelSelectedBoundary
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering from the same-embedding cyclic alternating edge/vertex face-boundary
walk layer plus per-face selected-boundary contiguity to the selected-boundary-contact shell on
the annulus construction side. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, boundaryGeom, hboundaryArc,
      hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
      hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData boundaryGeom hboundaryArc hnonPeelSelectedBoundary
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering from the honest facial closed-walk source layer plus per-face
selected-boundary contiguity to the selected-boundary-contact shell on the annulus construction
side. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, boundaryGeom, hboundaryArc,
      hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
      hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData boundaryGeom hboundaryArc hnonPeelSelectedBoundary
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering from the same-embedding ordered face-arc boundary geometry route plus
live interior-dual adjacency-distance peel data to the reduced positive-frontier shell. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      Nonempty (PlanarBoundaryOrderedFaceArcEmbeddingData emb) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionPositiveFrontierData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, ⟨boundaryGeom⟩,
      hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
      hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData boundaryGeom hnonPeelSelectedBoundary
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering from the same-embedding cyclic ordered face-arc boundary geometry route
plus live interior-dual adjacency-distance peel data to the reduced positive-frontier shell. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionPositiveFrontierData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, ⟨boundaryGeom⟩,
      hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
      hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData boundaryGeom hnonPeelSelectedBoundary
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering from the same-embedding cyclic alternating edge/vertex face-boundary
walk layer plus per-face selected-boundary contiguity to the reduced positive-frontier shell. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionPositiveFrontierData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, boundaryGeom, hboundaryArc,
      hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
      hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData boundaryGeom hboundaryArc hnonPeelSelectedBoundary
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Graph-level lowering from the honest facial closed-walk source layer plus per-face
selected-boundary contiguity to the reduced positive-frontier shell. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstructionPositiveFrontierData G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, boundaryGeom, hboundaryArc,
      hnonPeelSelectedBoundary, hcurrentOuterBoundaryNonempty,
      hcurrentOuterBoundaryDisjoint⟩
  exact
    ⟨emb, ⟨
      planarBoundaryAnnulusConstructionPositiveFrontierData_of_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData boundaryGeom hboundaryArc hnonPeelSelectedBoundary
        hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint⟩⟩

/-- Direct graph-level lowering from the same-embedding ordered face-arc boundary geometry route
plus live interior-dual adjacency-distance peel data to the annulus BFS construction target. -/
theorem
    admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      Nonempty (PlanarBoundaryOrderedFaceArcEmbeddingData emb) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  exact
    admitsPlanarBoundaryAnnulusConstruction_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
      (admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
        hG)

/-- Direct graph-level lowering from the same-embedding cyclic ordered face-arc boundary geometry
route plus live interior-dual adjacency-distance peel data to the annulus BFS construction target. -/
theorem
    admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  exact
    admitsPlanarBoundaryAnnulusConstruction_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
      (admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
        hG)

/-- Direct graph-level lowering from the same-embedding cyclic alternating edge/vertex
face-boundary walk layer plus per-face selected-boundary contiguity to the annulus BFS
construction target. -/
theorem
    admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  exact
    admitsPlanarBoundaryAnnulusConstruction_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
      (admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        hG)

/-- Direct graph-level lowering from the honest facial closed-walk source layer plus per-face
selected-boundary contiguity to the annulus BFS construction target. -/
theorem
    admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  exact
    admitsPlanarBoundaryAnnulusConstruction_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
      (admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        hG)

/-- Direct graph-level lowering from the same-embedding ordered face-arc boundary geometry route
plus live interior-dual adjacency-distance peel data to the pure annulus decomposition target. -/
theorem
    admitsPlanarBoundaryAnnulusDecomposition_of_exists_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      Nonempty (PlanarBoundaryOrderedFaceArcEmbeddingData emb) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  exact
    admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
      (admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_orderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
        hG)

/-- Direct graph-level lowering from the same-embedding cyclic ordered face-arc boundary geometry
route plus live interior-dual adjacency-distance peel data to the pure annulus decomposition
target. -/
theorem
    admitsPlanarBoundaryAnnulusDecomposition_of_exists_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  exact
    admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
      (admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_interiorDualBoundaryRootAdjDistancePeelData
        hG)

/-- Direct graph-level lowering from the same-embedding cyclic alternating edge/vertex
face-boundary walk layer plus per-face selected-boundary contiguity to the pure annulus
decomposition target. -/
theorem
    admitsPlanarBoundaryAnnulusDecomposition_of_exists_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryCyclicFaceBoundaryVertexWalkGeometry emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  exact
    admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
      (admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_cyclicFaceBoundaryVertexWalkGeometry_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        hG)

/-- Direct graph-level lowering from the honest facial closed-walk source layer plus per-face
selected-boundary contiguity to the pure annulus decomposition target. -/
theorem
    admitsPlanarBoundaryAnnulusDecomposition_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j))) :
    AdmitsPlanarBoundaryAnnulusDecomposition G := by
  exact
    admitsPlanarBoundaryAnnulusDecomposition_of_admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData
      (admitsPlanarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData
        hG)

/-- A pure annulus decomposition already contains the ambient outer/inner boundary split needed by
the BFS construction layer. Combining it with the live interior-dual adjacency-distance peel data
therefore yields an annulus construction on the same embedding without introducing any extra
boundary-side assumptions. -/
noncomputable def
    planarBoundaryAnnulusConstruction_of_annulusDecomposition_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (decomp : PlanarBoundaryAnnulusDecomposition emb)
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    PlanarBoundaryAnnulusConstruction emb :=
  planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    decomp.toPlanarBoundaryAnnulusBoundaryData data

/-- Direct same-embedding constructor from the live annulus-side outer-boundary-root BFS package.
This keeps the boundary split and interior-dual adjacency-distance data synchronized on the same
plane embedding while targeting the new annulus construction layer. -/
noncomputable def
    planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb) :
    PlanarBoundaryAnnulusConstruction emb :=
  planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    data.boundaryData data.interiorData

theorem
    nonPeelSelectedBoundary_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb) :
    ∀ f : AmbientFace emb.faces,
      f ∉
          (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
            data).peelFaces →
        ∃ e ∈ emb.faceBoundary f.1,
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces := by
  intro f hf
  simpa [planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData]
    using data.exists_mem_selectedBoundarySupport_of_not_mem_peelFaces (f := f) hf

theorem
    faces_subset_outerBoundaryFaces_union_peelFaces_union_innerBoundaryFaces_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryOuterBoundaryRootAdjDistancePeelData emb) :
    emb.faces.attach ⊆
      (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
          data).outerBoundaryFaces ∪
        (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
            data).peelFaces ∪
          (planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
              data).innerBoundaryFaces := by
  let c := planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
    data
  exact
    c.faces_subset_outerBoundaryFaces_union_peelFaces_union_innerBoundaryFaces_of_nonPeelSelectedBoundary
      (nonPeelSelectedBoundary_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData data)

/-- Direct same-embedding lowering from the reachability-based annulus boundary split and live
outer-boundary-root interior-dual data to the selected-boundary-contact construction shell.
The non-peeled selected-boundary condition is derived internally from the stronger fact that every
non-peeled face is forced onto the distinguished outer boundary face layer. -/
noncomputable def
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hboundaryReachable : ∀ f : AmbientFace emb.faces,
      BoundaryComponentReachableOnFace (emb := emb) f)
    (hrootsOuterBoundary : ∀ r ∈ interiorData.roots,
      ∃ e ∈ emb.faceBoundary r.1,
        e ∈ boundaryData.toPlanarBoundaryAnnulusBoundaryData.outerAmbientBoundary)
    (hcurrentOuterBoundaryNonempty :
      ∀ i :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars,
        0 < i.1 →
          ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).currentOuterBoundary i).Nonempty)
    (hcurrentOuterBoundaryDisjoint :
      ∀ {i j :
          Fin
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).numCollars},
        0 < i.1 → 0 < j.1 → i ≠ j →
          Disjoint
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i)
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary j)) :
    PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb := by
  let outerData :=
    planarBoundaryOuterBoundaryRootAdjDistancePeelData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_rootsOuterAmbientBoundary
      boundaryData interiorData hrootsOuterBoundary
  exact
    planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData hboundaryReachable
      (by
        intro f hf
        simpa [outerData,
          planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData,
          planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData]
          using
            nonPeelSelectedBoundary_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
              outerData f hf)
      hcurrentOuterBoundaryNonempty hcurrentOuterBoundaryDisjoint

/-- Graph-level lowering from the live outer-boundary-root adjacency-distance endpoint to the BFS
annulus construction target. -/
theorem admitsPlanarBoundaryAnnulusConstruction_of_admitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryOuterBoundaryRootAdjDistancePeelData G) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryAnnulusConstruction_of_planarBoundaryOuterBoundaryRootAdjDistancePeelData
      data⟩⟩

/-- Explicit same-embedding lowering from an abstract annulus boundary split plus live
interior-dual adjacency-distance peel data to the annulus BFS construction target. This is the
construction-layer route geometry should use once it can build the annulus boundary split on the
same embedding as the interior-dual BFS witness. -/
theorem
    admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryData emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, ⟨boundaryData⟩, ⟨interiorData⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryAnnulusConstruction_of_boundaryData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData⟩⟩

/-- Explicit same-embedding lowering from an actual annulus decomposition plus live interior-dual
adjacency-distance peel data to the annulus BFS construction target. This removes the remaining
need to supply the decomposition's ambient boundary split as a separate input. -/
theorem
    admitsPlanarBoundaryAnnulusConstruction_of_exists_annulusDecomposition_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusDecomposition emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, ⟨decomp⟩, ⟨interiorData⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryAnnulusConstruction_of_annulusDecomposition_and_interiorDualBoundaryRootAdjDistancePeelData
      decomp interiorData⟩⟩

/-- Explicit same-embedding lowering from a concrete boundary-component reachability witness plus
live interior-dual adjacency-distance peel data to the annulus BFS construction target. -/
theorem
    admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, ⟨boundaryData⟩, ⟨interiorData⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData⟩⟩

/-- Explicit same-embedding lowering from a concrete boundary-component reachability witness plus
the corrected root-free interior-dual height-parent package to the annulus BFS construction
target. This is the live constructive replacement for the inconsistent outer-boundary-root route.
-/
theorem
    admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryReachabilityData_and_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (InteriorDualHeightParentPeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAnnulusConstruction G := by
  rcases hG with ⟨emb, ⟨boundaryData⟩, ⟨interiorData⟩⟩
  exact ⟨emb, ⟨
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
      boundaryData interiorData⟩⟩

/-- Exact strengthened continuation theorem on the repaired root-free interior-dual route: shared-
endpoint boundary reachability together with height-parent data already reaches the honest
construction-side orientation surface, not just the weaker annulus construction shell. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (InteriorDualHeightParentPeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation G := by
  rcases hG with ⟨emb, ⟨boundaryData⟩, ⟨interiorData⟩⟩
  refine ⟨emb, ?_, ?_⟩
  · exact
      planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
        boundaryData interiorData
  · exact
      parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
        boundaryData interiorData

/-- Direct theorem-4.9-facing lowering from the repaired root-free interior-dual height-parent
route. This is the strongest currently positive same-embedding continuation theorem on the live
annulus-construction route. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_boundaryReachabilityData_and_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (InteriorDualHeightParentPeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
      (admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_interiorDualHeightParentPeelData
        hG)

/-- Corrected parent-oriented continuation from the boundary-root adjacency-distance source. The
shifted collar-indexing construction still needs a first-collar exclusion for parent orientation,
but the same source data also gives this root-distance construction, whose face distances are the
unshifted interior-dual distances and which is parent-oriented without an extra positivity
hypothesis. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation G := by
  rcases hG with ⟨emb, ⟨boundaryData⟩, ⟨interiorData⟩⟩
  refine ⟨emb, ?_, ?_⟩
  · exact
      planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        boundaryData interiorData
  · exact
      parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_rootDistance
        boundaryData interiorData

/-- Direct theorem-4.9-facing continuation from the boundary-root adjacency-distance source via the
root-distance construction. This is the positive replacement for trying to orient the shifted
collar-indexing construction itself. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
      (admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        hG)

/-- Direct annihilator theorem on the repaired root-free interior-dual height-parent source shell.
This packages the strongest currently positive theorem-4.9 route without detouring through the
intermediate annulus-construction existence predicate. -/
theorem
    zero_on_allEdges_of_exists_boundaryReachabilityData_and_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ interiorData : InteriorDualHeightParentPeelData emb.faces emb.faceBoundary,
          (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
          (∀ f ∈
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
                boundaryData interiorData).peelFaces,
            ∀ γ, γ ≠ 0 →
              γ ≠ C
                ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
                  boundaryData interiorData).witnessEdge f) →
              chainDot
                  (boundaryBicoloredEdges C
                    (C
                      ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
                        boundaryData interiorData).witnessEdge f))
                    (C
                      ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
                        boundaryData interiorData).witnessEdge f) + γ)
                    (emb.faceBoundary f.1))
                  z
                  (polarizedFaceGenerator C
                    (C
                      ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
                        boundaryData interiorData).witnessEdge f))
                    (C
                      ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
                        boundaryData interiorData).witnessEdge f) + γ)
                    (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, boundaryData, interiorData, hzeroBoundary, horth⟩
  let data :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
      boundaryData interiorData
  have horient : data.ParentWitnessOrientation :=
    parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualHeightParentPeelData
      boundaryData interiorData
  exact
    zero_on_allEdges_of_planarBoundaryAnnulusConstruction_of_parentWitness
      (emb := emb) (data := data) (hparentWitness := horient)
      (C := C) (htait := htait) (z := z)
      (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Exact strengthened continuation theorem on the live shifted boundary-root adjacency-distance
route: shared-endpoint boundary reachability plus the interior-dual data reach the honest
construction-side orientation surface precisely after adding positivity of annulus construction
distance on every peeled face. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_pos_faceDistance
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
          ∀ g ∈ interiorData.peelFaces,
            0 <
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).faceDistance g) :
    AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation G := by
  rcases hG with ⟨emb, boundaryData, interiorData, hpos⟩
  refine ⟨emb, ?_, ?_⟩
  · exact
      planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData
  · exact
      parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_pos_faceDistance
        boundaryData interiorData hpos

/-- Direct theorem-4.9-facing lowering from the live shifted boundary-root adjacency-distance
route once first-collar peeled faces are excluded by positivity of annulus construction distance.
This is the exact strengthened continuation theorem on the paper-facing source shell. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_pos_faceDistance
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
          ∀ g ∈ interiorData.peelFaces,
            0 <
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).faceDistance g) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
      (admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_pos_faceDistance
        hG)

/-- Exact strengthened continuation theorem on the live shifted boundary-root adjacency-distance
route in structural source language: it is enough that every peeled face has a canonical
`parentTowardsRoot` predecessor that is itself peeled. This is equivalent to the earlier positive
shifted-distance condition but stated directly on the original interior-dual data. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
          ∀ g ∈ interiorData.peelFaces,
            ∃ p ∈ interiorData.peelFaces,
              parentTowardsRoot
                  (interiorDualSpanningForest emb.faceBoundary emb.faces)
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces interiorData.roots
                    interiorData.hcoverRoots interiorData.hsepRoots)
                  g = some p) :
    AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation G := by
  rcases hG with ⟨emb, ⟨boundaryData⟩, interiorData, hparent⟩
  let data :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData
  have horient : data.ParentWitnessOrientation := by
    have hiff :=
      parentWitnessOrientation_iff_exists_parent_mem_peelFaces_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData
    exact hiff.2 hparent
  exact ⟨emb, data, horient⟩

/-- Structural theorem-4.9 continuation on the live shifted boundary-root adjacency-distance
source shell: it is enough that every peeled face has a canonical `parentTowardsRoot`
predecessor that is itself peeled. This is equivalent to the earlier positive shifted-distance
condition but stated directly on the original interior-dual data. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
          ∀ g ∈ interiorData.peelFaces,
            ∃ p ∈ interiorData.peelFaces,
              parentTowardsRoot
                  (interiorDualSpanningForest emb.faceBoundary emb.faces)
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces interiorData.roots
                    interiorData.hcoverRoots interiorData.hsepRoots)
                  g = some p) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
      (admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
        hG)

/-- Direct annihilator theorem on the exact strengthened shifted boundary-root adjacency-distance
surface. This packages the theorem-4.9 continuation route for the paper-facing source shell once
first-collar peeled faces are excluded by positivity of annulus construction distance. -/
theorem
    zero_on_allEdges_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_pos_faceDistance
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
          (∀ g ∈ interiorData.peelFaces,
            0 <
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).faceDistance g) ∧
          (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
          (∀ f ∈
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces,
            ∀ γ, γ ≠ 0 →
              γ ≠ C
                ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).witnessEdge f) →
              chainDot
                  (boundaryBicoloredEdges C
                    (C
                      ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                        boundaryData interiorData).witnessEdge f))
                    (C
                      ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                        boundaryData interiorData).witnessEdge f) + γ)
                    (emb.faceBoundary f.1))
                  z
                  (polarizedFaceGenerator C
                    (C
                      ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                        boundaryData interiorData).witnessEdge f))
                    (C
                      ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                        boundaryData interiorData).witnessEdge f) + γ)
                    (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, boundaryData, interiorData, hpos, hzeroBoundary, horth⟩
  let data :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData
  have horient :
      data.ParentWitnessOrientation :=
    parentWitnessOrientation_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_of_pos_faceDistance
      boundaryData interiorData hpos
  exact
    zero_on_allEdges_of_planarBoundaryAnnulusConstruction_of_parentWitness
      (emb := emb) (data := data) (hparentWitness := horient)
      (C := C) (htait := htait) (z := z)
      (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Direct annihilator theorem on the structural shifted boundary-root adjacency-distance
surface. It is enough that every peeled face has a canonical `parentTowardsRoot` predecessor that
is itself peeled. This is equivalent to the earlier positive shifted-distance condition but keeps
the theorem surface in the original interior-dual language. -/
theorem
    zero_on_allEdges_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
          (∀ g ∈ interiorData.peelFaces,
            ∃ p ∈ interiorData.peelFaces,
              parentTowardsRoot
                  (interiorDualSpanningForest emb.faceBoundary emb.faces)
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces interiorData.roots
                    interiorData.hcoverRoots interiorData.hsepRoots)
                  g = some p) ∧
          (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
          (∀ f ∈
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces,
            ∀ γ, γ ≠ 0 →
              γ ≠ C
                ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).witnessEdge f) →
              chainDot
                  (boundaryBicoloredEdges C
                    (C
                      ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                        boundaryData interiorData).witnessEdge f))
                    (C
                      ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                        boundaryData interiorData).witnessEdge f) + γ)
                    (emb.faceBoundary f.1))
                  z
                  (polarizedFaceGenerator C
                    (C
                      ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                        boundaryData interiorData).witnessEdge f))
                    (C
                      ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                        boundaryData interiorData).witnessEdge f) + γ)
                    (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with ⟨emb, boundaryData, interiorData, hparent, hzeroBoundary, horth⟩
  let data :=
    planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
      boundaryData interiorData
  have horient : data.ParentWitnessOrientation := by
    have hiff :=
      parentWitnessOrientation_iff_exists_parent_mem_peelFaces_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        boundaryData interiorData
    exact hiff.2 hparent
  exact
    zero_on_allEdges_of_planarBoundaryAnnulusConstruction_of_parentWitness
      (emb := emb) (data := data) (hparentWitness := horient)
      (C := C) (htait := htait) (z := z)
      (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Exact strengthened continuation theorem on the strongest currently honest walk-anchored
adjacency-distance source shell. Once the interior-dual peeled-parent condition holds, the same
closed-walk-plus-selected-arc geometry reaches the construction-side parent-witness orientation
surface. -/
theorem
    admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j)) ∧
        (∀ g ∈ interiorData.peelFaces,
          ∃ p ∈ interiorData.peelFaces,
            parentTowardsRoot
                (interiorDualSpanningForest emb.faceBoundary emb.faces)
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces interiorData.roots
                  interiorData.hcoverRoots interiorData.hsepRoots)
                g = some p)) :
    AdmitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation G := by
  rcases hG with
    ⟨emb, boundaryData, interiorData, boundaryGeom, hboundaryArc, hnonPeelSelectedBoundary,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint, hparent⟩
  exact
    admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
      ⟨emb, ⟨boundaryData⟩, interiorData, hparent⟩

/-- Direct theorem-4.9-facing lowering from the honest facial closed-walk source layer plus the
exact peeled-parent repair on the live adjacency-distance route. -/
theorem
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j)) ∧
        (∀ g ∈ interiorData.peelFaces,
          ∃ p ∈ interiorData.peelFaces,
            parentTowardsRoot
                (interiorDualSpanningForest emb.faceBoundary emb.faces)
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces interiorData.roots
                  interiorData.hcoverRoots interiorData.hsepRoots)
                g = some p)) :
    AdmitsPlanarBoundaryWellFoundedFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryWellFoundedFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation
      (admitsPlanarBoundaryAnnulusConstructionParentWitnessOrientation_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
        hG)

/-- Direct annihilator theorem on the strongest currently honest walk-anchored adjacency-distance
source shell, with the exact peeled-parent repair added explicitly. -/
theorem
    zero_on_allEdges_of_exists_boundaryReachabilityData_and_closedWalkEmbeddingData_and_selectedBoundaryArcOnFace_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (hdata : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ interiorData : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary,
      ∃ boundaryGeom : PlanarBoundaryClosedWalkEmbeddingData emb,
        (∀ f : AmbientFace emb.faces,
          (boundaryGeom.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f) ∧
        (∀ f : AmbientFace emb.faces,
          f ∉
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).peelFaces →
            ∃ e ∈ emb.faceBoundary f.1,
              e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) ∧
        (∀ i :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars,
          0 < i.1 →
            ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).currentOuterBoundary i).Nonempty) ∧
        (∀ {i j :
            Fin
              (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).numCollars},
          0 < i.1 → 0 < j.1 → i ≠ j →
            Disjoint
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary i)
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                  boundaryData interiorData).currentOuterBoundary j)) ∧
        (∀ g ∈ interiorData.peelFaces,
          ∃ p ∈ interiorData.peelFaces,
            parentTowardsRoot
                (interiorDualSpanningForest emb.faceBoundary emb.faces)
                (interiorDualSpanningForestRoot emb.faceBoundary emb.faces interiorData.roots
                  interiorData.hcoverRoots interiorData.hsepRoots)
                g = some p) ∧
        (∀ e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces, z e = 0) ∧
        (∀ f ∈
            (planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
              boundaryData interiorData).peelFaces,
          ∀ γ, γ ≠ 0 →
            γ ≠ C
              ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                boundaryData interiorData).witnessEdge f) →
            chainDot
                (boundaryBicoloredEdges C
                  (C
                    ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                      boundaryData interiorData).witnessEdge f))
                  (C
                    ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                      boundaryData interiorData).witnessEdge f) + γ)
                  (emb.faceBoundary f.1))
                z
                (polarizedFaceGenerator C
                  (C
                    ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                      boundaryData interiorData).witnessEdge f))
                  (C
                    ((planarBoundaryAnnulusConstruction_of_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
                      boundaryData interiorData).witnessEdge f) + γ)
                  (emb.faceBoundary f.1)) = 0)) :
    ∀ e, z e = 0 := by
  rcases hdata with
    ⟨emb, boundaryData, interiorData, boundaryGeom, hboundaryArc, hnonPeelSelectedBoundary,
      hcurrentOuterBoundaryNonempty, hcurrentOuterBoundaryDisjoint, hparent, hzeroBoundary, horth⟩
  exact
    zero_on_allEdges_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData_and_parentInPeelFaces
      (C := C) (htait := htait) (z := z)
      ⟨emb, boundaryData, interiorData, hparent, hzeroBoundary, horth⟩

/-- Direct theorem-4.9-facing lowering from same-embedding boundary-component reachability plus
live interior-dual adjacency-distance peel data to the finite collar-layer witness package,
without requiring users to compose through the annulus construction layer manually. -/
theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstruction
      (admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryReachabilityData_and_interiorDualBoundaryRootAdjDistancePeelData
        hG)

/-- Direct theorem-4.9-facing lowering from same-embedding boundary-component reachability plus
the corrected root-free interior-dual height-parent package to the finite collar-layer witness
package. This makes the repaired live route explicit at the theorem surface. -/
theorem
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_exists_boundaryReachabilityData_and_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (InteriorDualHeightParentPeelData emb.faces emb.faceBoundary)) :
    AdmitsPlanarBoundaryCollarLayerFacePeelWitnessData G := by
  exact
    admitsPlanarBoundaryCollarLayerFacePeelWitnessData_of_admitsPlanarBoundaryAnnulusConstruction
      (admitsPlanarBoundaryAnnulusConstruction_of_exists_boundaryReachabilityData_and_interiorDualHeightParentPeelData
        hG)

end Mettapedia.GraphTheory.FourColor
