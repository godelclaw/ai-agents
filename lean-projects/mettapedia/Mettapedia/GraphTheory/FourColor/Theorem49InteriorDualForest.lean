import Mettapedia.GraphTheory.FourColor.FaceIncidence
import Mettapedia.GraphTheory.FourColor.Theorem49LocalRemainderBoundaryCollar
import Mettapedia.GraphTheory.FourColor.Theorem49RootedDistance

namespace Mettapedia.GraphTheory.FourColor

variable {V F : Type*} [DecidableEq V] [DecidableEq F]

/-- Boundary map on the subtype of ambient faces. -/
def ambientFaceBoundary {E : Type*} (faceBoundary : F → Finset E) {allFaces : Finset F} :
    AmbientFace allFaces → Finset E :=
  fun f => faceBoundary f.1

omit [DecidableEq F] in
theorem biUnion_attach_ambientFaceBoundary_eq {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F) :
    allFaces.attach.biUnion (ambientFaceBoundary (allFaces := allFaces) faceBoundary) =
      allFaces.biUnion faceBoundary := by
  ext e
  simp [ambientFaceBoundary]

omit [DecidableEq F] in
theorem totalIncidenceCount_ambientFaceBoundary_eq {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F) (e : E) :
    totalIncidenceCount (ambientFaceBoundary (allFaces := allFaces) faceBoundary)
        allFaces.attach e =
      totalIncidenceCount faceBoundary allFaces e := by
  simpa [totalIncidenceCount, ambientFaceBoundary] using
    congrArg Finset.card (Finset.filter_attach (p := fun f => e ∈ faceBoundary f) allFaces)

omit [DecidableEq F] in
theorem interiorEdgeSupport_ambientFaceBoundary_eq {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F) :
    interiorEdgeSupport (ambientFaceBoundary (allFaces := allFaces) faceBoundary) allFaces.attach =
      interiorEdgeSupport faceBoundary allFaces := by
  ext e
  simp [interiorEdgeSupport, biUnion_attach_ambientFaceBoundary_eq,
    totalIncidenceCount_ambientFaceBoundary_eq]

omit [DecidableEq F] in
theorem selectedBoundarySupport_ambientFaceBoundary_eq {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F) :
    selectedBoundarySupport
        (ambientFaceBoundary (allFaces := allFaces) faceBoundary)
        allFaces.attach allFaces.attach =
      selectedBoundarySupport faceBoundary allFaces allFaces := by
  ext e
  simp [selectedBoundarySupport, biUnion_attach_ambientFaceBoundary_eq,
    totalIncidenceCount_ambientFaceBoundary_eq]

/-- A canonical spanning forest of the interior dual graph, chosen from Lemma 4.6. -/
noncomputable def interiorDualSpanningForest {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F) :
    SimpleGraph (AmbientFace allFaces) :=
  Classical.choose (interiorDualGraph_exists_spanningForest faceBoundary allFaces)

omit [DecidableEq F] in
theorem interiorDualSpanningForest_le {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F) :
    interiorDualSpanningForest faceBoundary allFaces ≤ interiorDualGraph faceBoundary allFaces :=
  (Classical.choose_spec (interiorDualGraph_exists_spanningForest faceBoundary allFaces)).1

omit [DecidableEq F] in
theorem interiorDualSpanningForest_isAcyclic {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F) :
    (interiorDualSpanningForest faceBoundary allFaces).IsAcyclic :=
  (Classical.choose_spec (interiorDualGraph_exists_spanningForest faceBoundary allFaces)).2.1

omit [DecidableEq F] in
theorem interiorDualSpanningForest_reachable_eq {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F) :
    (interiorDualSpanningForest faceBoundary allFaces).Reachable =
      (interiorDualGraph faceBoundary allFaces).Reachable :=
  (Classical.choose_spec (interiorDualGraph_exists_spanningForest faceBoundary allFaces)).2.2

/-- Canonical root assignment on the chosen interior-dual spanning forest, induced by a set of
ambient dual roots that covers and separates connected components. -/
noncomputable def interiorDualSpanningForestRoot {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (roots : Finset (AmbientFace allFaces))
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots) :
    AmbientFace allFaces → AmbientFace allFaces :=
  uniqueReachableRoot (interiorDualSpanningForest faceBoundary allFaces) roots
    (hasUniqueReachableRoot_of_cover_and_separated
      (interiorDualSpanningForest faceBoundary allFaces) roots
      ((rootSetCovers_congr_reachable roots
        (interiorDualSpanningForest_reachable_eq faceBoundary allFaces)).2 hcoverRoots)
      ((rootSetSeparated_congr_reachable roots
        (interiorDualSpanningForest_reachable_eq faceBoundary allFaces)).2 hsepRoots))

omit [DecidableEq F] in
theorem interiorDualSpanningForestRoot_mem_roots {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (roots : Finset (AmbientFace allFaces))
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (f : AmbientFace allFaces) :
    interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f ∈ roots := by
  unfold interiorDualSpanningForestRoot
  exact uniqueReachableRoot_mem_roots _ _ _ _

omit [DecidableEq F] in
theorem reachable_interiorDualSpanningForestRoot {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (roots : Finset (AmbientFace allFaces))
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (f : AmbientFace allFaces) :
    (interiorDualSpanningForest faceBoundary allFaces).Reachable f
      (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f) := by
  unfold interiorDualSpanningForestRoot
  exact reachable_uniqueReachableRoot _ _ _ _

omit [DecidableEq F] in
theorem interiorDualSpanningForestRoot_eq_of_adj {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (roots : Finset (AmbientFace allFaces))
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    {f g : AmbientFace allFaces}
    (hfg : (interiorDualSpanningForest faceBoundary allFaces).Adj f g) :
    interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f =
      interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots g := by
  unfold interiorDualSpanningForestRoot
  exact uniqueReachableRoot_eq_of_adj _ _ _ hfg

omit [DecidableEq F] in
theorem ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots {E : Type*}
    [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hdisj : Disjoint peelFaces roots) {f : AmbientFace allFaces} (hf : f ∈ peelFaces) :
    f ≠ interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f := by
  intro hEq
  have hroot : interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f ∈ roots :=
    interiorDualSpanningForestRoot_mem_roots
      faceBoundary allFaces roots hcoverRoots hsepRoots f
  have hfroot :
      interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f ∈ peelFaces := by
    rw [← hEq]
    exact hf
  exact Finset.disjoint_left.mp hdisj hfroot hroot

omit [DecidableEq F] in
theorem disjoint_peelFaces_roots_of_boundarySeparation {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces) :
    Disjoint peelFaces roots := by
  refine Finset.disjoint_left.2 ?_
  intro f hf hfroot
  rcases hrootsBoundary f hfroot with ⟨e, hef, heboundary⟩
  exact (Finset.disjoint_left.mp (hpeelInterior f hf) hef) heboundary

/-- For a rooted parent map on the chosen interior-dual spanning forest, the witness edge of a
non-root face can be chosen canonically as the unique primal interior edge shared with its parent,
provided shared interior edges are pairwise unique. Faces without a parent use `fallbackEdge`,
which is irrelevant for the current peeling interfaces because only peeled non-root faces consume
the witness-edge data. -/
noncomputable def parentSharedInteriorEdgeOfPairwiseUnique
    {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → E)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p) :
    AmbientFace allFaces → E :=
  fun f =>
    if hfp : ∃ p, parentFace f = some p then
      sharedInteriorEdgeOfAdjOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForest_le faceBoundary allFaces <|
          hparentAdj (Classical.choose_spec hfp))
    else
      fallbackEdge f

/-- Canonical shared interior edge selected from the shortest-path parent toward a chosen root in
the interior-dual spanning forest. Faces without such a parent use `fallbackEdge`; on peeled
non-root faces this fallback is irrelevant because the shortest-path parent exists. -/
noncomputable def rootedSharedInteriorEdgeOfPairwiseUnique
    {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (rootFace : AmbientFace allFaces → AmbientFace allFaces)
    (fallbackEdge : AmbientFace allFaces → E) :
    AmbientFace allFaces → E :=
  parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
    (parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces) rootFace)
    fallbackEdge
    (by
      intro f p hfp
      exact parentTowardsRoot_some_adj
        (interiorDualSpanningForest faceBoundary allFaces) rootFace hfp)

theorem parentSharedInteriorEdgeOfPairwiseUnique_eq_sharedInteriorEdgeOfAdjOfPairwiseUnique
    {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → E)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    {f p : AmbientFace allFaces} (hfp : parentFace f = some p) :
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj f =
      sharedInteriorEdgeOfAdjOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForest_le faceBoundary allFaces <| hparentAdj hfp) := by
  unfold parentSharedInteriorEdgeOfPairwiseUnique
  let hp : ∃ p, parentFace f = some p := ⟨p, hfp⟩
  rw [dif_pos hp]
  have hs : some (Classical.choose hp) = some p := by
    exact (Classical.choose_spec hp).symm.trans hfp
  have hchoose : Classical.choose hp = p := by
    simpa using Option.some.inj hs
  have hspec : parentFace f = some p := by
    simpa [hchoose] using Classical.choose_spec hp
  simp [hchoose]

theorem parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
    {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → E)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    {f p : AmbientFace allFaces} (hfp : parentFace f = some p) :
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj f ∈ faceBoundary f.1 := by
  rw [parentSharedInteriorEdgeOfPairwiseUnique_eq_sharedInteriorEdgeOfAdjOfPairwiseUnique
    faceBoundary allFaces hunique parentFace fallbackEdge hparentAdj hfp]
  exact sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_left
    faceBoundary allFaces hunique
    (interiorDualSpanningForest_le faceBoundary allFaces <| hparentAdj hfp)

theorem parentSharedInteriorEdgeOfPairwiseUnique_mem_parent_faceBoundary
    {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → E)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    {f p : AmbientFace allFaces} (hfp : parentFace f = some p) :
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj f ∈ faceBoundary p.1 := by
  rw [parentSharedInteriorEdgeOfPairwiseUnique_eq_sharedInteriorEdgeOfAdjOfPairwiseUnique
    faceBoundary allFaces hunique parentFace fallbackEdge hparentAdj hfp]
  exact sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
    faceBoundary allFaces hunique
    (interiorDualSpanningForest_le faceBoundary allFaces <| hparentAdj hfp)

theorem parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
    {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → E)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    {f g : AmbientFace allFaces} (hgf : parentFace g = some f)
    {e : E} (heg : e ∈ faceBoundary g.1) (hef : e ∈ faceBoundary f.1) :
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj g = e := by
  rw [parentSharedInteriorEdgeOfPairwiseUnique_eq_sharedInteriorEdgeOfAdjOfPairwiseUnique
    faceBoundary allFaces hunique parentFace fallbackEdge hparentAdj hgf]
  have hshared : e ∈ sharedInteriorEdges faceBoundary allFaces g.1 f.1 := by
    apply (mem_sharedInteriorEdges_iff faceBoundary allFaces).2
    refine ⟨?_, heg, hef⟩
    apply (mem_interiorEdgeSupport_iff faceBoundary allFaces).2
    refine ⟨Finset.mem_biUnion.2 ⟨g.1, g.2, heg⟩, ?_⟩
    apply totalIncidenceCount_eq_two_of_mem_faceBoundary_of_mem_faceBoundary_of_ne
      faceBoundary allFaces hall g.2 f.2
    · exact (interiorDualGraph_adj_iff faceBoundary allFaces).1
        (interiorDualSpanningForest_le faceBoundary allFaces (hparentAdj hgf)) |>.1
    · exact heg
    · exact hef
  exact sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
    faceBoundary allFaces hunique
    (interiorDualSpanningForest_le faceBoundary allFaces (hparentAdj hgf))
    hshared

/-- Canonical interior-dual-spanning-forest specialization of the current Theorem 4.9 route. This
packages the chosen forest from Lemma 4.6 and transfers root coverage/separation from the ambient
interior dual graph to that forest; the remaining burden is then purely the annulus geometry:
provide the root set, witness edges, and the local child-edge/distance condition on the forest. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedRootsAdjDistanceWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (witnessEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f.1)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest faceBoundary allFaces).Adj f g ∧
          witnessEdge g = e ∧
          (interiorDualSpanningForest faceBoundary allFaces).dist
              f (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest faceBoundary allFaces).dist
              g (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let subBoundary : AmbientFace allFaces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := allFaces) faceBoundary
  have hcover' :
      interiorEdgeSupport subBoundary allFaces.attach ⊆ peelFaces.image witnessEdge := by
    simpa [subBoundary, interiorEdgeSupport_ambientFaceBoundary_eq] using hcover
  have hwitness' : ∀ f ∈ peelFaces, witnessEdge f ∈ subBoundary f := by
    intro f hf
    simpa [subBoundary, ambientFaceBoundary] using hwitness f hf
  have hchildren' :
      ∀ f ∈ peelFaces, ∀ e ∈ (subBoundary f).erase (witnessEdge f),
        e ∈ selectedBoundarySupport subBoundary allFaces.attach allFaces.attach ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest faceBoundary allFaces).Adj f g ∧
            witnessEdge g = e ∧
            (interiorDualSpanningForest faceBoundary allFaces).dist
                f (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f) <
              (interiorDualSpanningForest faceBoundary allFaces).dist
                g (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots g) := by
    intro f hf e he
    rcases hchildren f hf e (by simpa [subBoundary, ambientFaceBoundary] using he) with
      hboundary | hchild
    · left
      simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using hboundary
    · exact Or.inr hchild
  have hall' : ∀ e, totalIncidenceCount subBoundary allFaces.attach e ≤ 2 := by
    intro e
    simpa [subBoundary, totalIncidenceCount_ambientFaceBoundary_eq] using hall e
  have hzeroBoundary' :
      ∀ e ∈ selectedBoundarySupport subBoundary allFaces.attach allFaces.attach, z e = 0 := by
    intro e he
    exact hzeroBoundary e (by simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using he)
  have horth' :
      ∀ f ∈ peelFaces,
        ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
                (subBoundary f))
              z
              (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
                (subBoundary f)) = 0 := by
    intro f hf γ hγ0 hγd
    simpa [subBoundary, ambientFaceBoundary] using horth f hf γ hγ0 hγd
  simpa [subBoundary, biUnion_attach_ambientFaceBoundary_eq] using
    zero_on_ambientFaceSupport_of_coverSeparatedRootsAdjDistanceWitnessCover_of_reachableEq
      (C := C) (htait := htait) (z := z)
      (T := interiorDualSpanningForest faceBoundary allFaces)
      (T' := interiorDualGraph faceBoundary allFaces)
      (allFaces := allFaces.attach) (peelFaces := peelFaces) (roots := roots)
      (faceBoundary := subBoundary) (witnessEdge := witnessEdge)
      (hAcyc := interiorDualSpanningForest_isAcyclic faceBoundary allFaces)
      (hreachEq := interiorDualSpanningForest_reachable_eq faceBoundary allFaces)
      (hcoverRoots := hcoverRoots) (hsepRoots := hsepRoots)
      hcover' hwitness' hchildren' hall' hzeroBoundary' horth'

/-- Root-face version of the interior-dual-spanning-forest wrapper. Instead of supplying a
separate finite root set together with cover/separation proofs, it is enough to assign each peeled
face a designated root face in the ambient interior dual, require reachability to that root in the
ambient dual, and require the root assignment to be constant along edges of the chosen spanning
forest. The acyclic forest then still supplies the distance and child-adjacency data used by the
peeling argument. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_adjInvariantRootedAdjDistanceWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (rootFace : AmbientFace allFaces → AmbientFace allFaces)
    (witnessEdge : AmbientFace allFaces → G.edgeSet)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image witnessEdge)
    (hreach : ∀ f ∈ peelFaces,
      (interiorDualGraph faceBoundary allFaces).Reachable f (rootFace f))
    (hrootAdj : ∀ ⦃f g : AmbientFace allFaces⦄,
      (interiorDualSpanningForest faceBoundary allFaces).Adj f g → rootFace f = rootFace g)
    (hwitness : ∀ f ∈ peelFaces, witnessEdge f ∈ faceBoundary f.1)
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase (witnessEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest faceBoundary allFaces).Adj f g ∧
          witnessEdge g = e ∧
          (interiorDualSpanningForest faceBoundary allFaces).dist f (rootFace f) <
            (interiorDualSpanningForest faceBoundary allFaces).dist g (rootFace g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
        chainDot
            (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let subBoundary : AmbientFace allFaces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := allFaces) faceBoundary
  have hcover' :
      interiorEdgeSupport subBoundary allFaces.attach ⊆ peelFaces.image witnessEdge := by
    simpa [subBoundary, interiorEdgeSupport_ambientFaceBoundary_eq] using hcover
  have hwitness' : ∀ f ∈ peelFaces, witnessEdge f ∈ subBoundary f := by
    intro f hf
    simpa [subBoundary, ambientFaceBoundary] using hwitness f hf
  have hchildren' :
      ∀ f ∈ peelFaces, ∀ e ∈ (subBoundary f).erase (witnessEdge f),
        e ∈ selectedBoundarySupport subBoundary allFaces.attach allFaces.attach ∨
          ∃ g ∈ peelFaces,
            (interiorDualSpanningForest faceBoundary allFaces).Adj f g ∧
            witnessEdge g = e ∧
            (interiorDualSpanningForest faceBoundary allFaces).dist f (rootFace f) <
              (interiorDualSpanningForest faceBoundary allFaces).dist g (rootFace g) := by
    intro f hf e he
    rcases hchildren f hf e (by simpa [subBoundary, ambientFaceBoundary] using he) with
      hboundary | hchild
    · left
      simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using hboundary
    · exact Or.inr hchild
  have hall' : ∀ e, totalIncidenceCount subBoundary allFaces.attach e ≤ 2 := by
    intro e
    simpa [subBoundary, totalIncidenceCount_ambientFaceBoundary_eq] using hall e
  have hzeroBoundary' :
      ∀ e ∈ selectedBoundarySupport subBoundary allFaces.attach allFaces.attach, z e = 0 := by
    intro e he
    exact hzeroBoundary e
      (by simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using he)
  have horth' :
      ∀ f ∈ peelFaces,
        ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
                (subBoundary f))
              z
              (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
                (subBoundary f)) = 0 := by
    intro f hf γ hγ0 hγd
    simpa [subBoundary, ambientFaceBoundary] using horth f hf γ hγ0 hγd
  simpa [subBoundary, biUnion_attach_ambientFaceBoundary_eq] using
    zero_on_ambientFaceSupport_of_adjInvariantRootedAdjDistanceWitnessCover_of_reachableEq
      (C := C) (htait := htait) (z := z)
      (T := interiorDualSpanningForest faceBoundary allFaces)
      (T' := interiorDualGraph faceBoundary allFaces)
      (allFaces := allFaces.attach) (peelFaces := peelFaces)
      (faceBoundary := subBoundary) (rootFace := rootFace) (witnessEdge := witnessEdge)
      (hAcyc := interiorDualSpanningForest_isAcyclic faceBoundary allFaces)
      (hreachEq := interiorDualSpanningForest_reachable_eq faceBoundary allFaces)
      hcover' hreach hrootAdj hwitness' hchildren' hall' hzeroBoundary' horth'

/-- Parent-edge specialization of the interior-dual-spanning-forest wrapper. Under pairwise
uniqueness of shared interior edges, the witness edge of each peeled face is determined by the
primal edge shared with its parent in the rooted forest, so the remaining local condition only has
to specify which children own the other non-boundary edges. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedRoots_parentSharedEdgeWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧
          parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
            parentFace fallbackEdge hparentAdj g = e ∧
          (interiorDualSpanningForest faceBoundary allFaces).dist
              f (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest faceBoundary allFaces).dist
              g (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
      parentFace fallbackEdge hparentAdj
  apply zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedRootsAdjDistanceWitnessCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces)
    (peelFaces := peelFaces) (roots := roots) (faceBoundary := faceBoundary)
    (witnessEdge := witnessEdge) hcoverRoots hsepRoots
  · simpa [witnessEdge] using hcover
  · intro f hf
    rcases hparent f hf with ⟨p, hfp⟩
    simpa [witnessEdge] using
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces hunique parentFace fallbackEdge hparentAdj hfp
  · intro f hf e he
    rcases hchildren f hf e (by simpa [witnessEdge] using he) with hboundary | ⟨g, hg, hgf, hge, hlt⟩
    · exact Or.inl hboundary
    · exact Or.inr ⟨g, hg, (hparentAdj hgf).symm, by simpa [witnessEdge] using hge, hlt⟩
  · exact hall
  · exact hzeroBoundary
  · intro f hf γ hγ0 hγd
    simpa [witnessEdge] using horth f hf γ hγ0 hγd

/-- Primal-face-membership version of the parent-edge specialization. Instead of requiring the
child witness edge to be named explicitly, it is enough to know that the candidate edge lies on
both the peeled face and a child face whose parent is that peeled face; pairwise uniqueness then
identifies that edge with the child's canonical parent-shared witness edge. This is closer to the
paper's Step 2 wording, which is stated in terms of primal face boundaries rather than pre-chosen
witness functions on children. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedRoots_parentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧
          e ∈ faceBoundary g.1 ∧
          (interiorDualSpanningForest faceBoundary allFaces).dist
              f (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest faceBoundary allFaces).dist
              g (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  apply zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedRoots_parentSharedEdgeWitnessCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces)
    (peelFaces := peelFaces) (roots := roots) (faceBoundary := faceBoundary)
    (hunique := hunique) (parentFace := parentFace) (fallbackEdge := fallbackEdge)
    (hparent := hparent) (hparentAdj := hparentAdj)
    (hcoverRoots := hcoverRoots) (hsepRoots := hsepRoots)
    (hcover := hcover) (hall := hall) (hzeroBoundary := hzeroBoundary) (horth := horth)
  intro f hf e he
  rcases hchildren f hf e he with hboundary | ⟨g, hg, hgf, heg, hlt⟩
  · exact Or.inl hboundary
  · refine Or.inr ⟨g, hg, hgf, ?_, hlt⟩
    exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
      faceBoundary allFaces hunique parentFace fallbackEdge hparentAdj hall hgf heg
      ((Finset.mem_erase.1 he).2)

/-- Height-ordered specialization of the interior-dual-spanning-forest route. Once the peeled
faces come with a parent map in the chosen forest and a height function that strictly increases
along parent edges, the Theorem 4.9 annihilator step no longer needs any auxiliary root data:
the canonical parent-shared witness edges and the automatic decreasing-height peel order suffice. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_heightOrdered_parentSharedEdgeWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (height : AmbientFace allFaces → ℕ)
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧
          parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
            parentFace fallbackEdge hparentAdj g = e)
    (hheight : ∀ g ∈ peelFaces, ∀ f, parentFace g = some f → height f < height g)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let subBoundary : AmbientFace allFaces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := allFaces) faceBoundary
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
      parentFace fallbackEdge hparentAdj
  have hcover' :
      interiorEdgeSupport subBoundary allFaces.attach ⊆ peelFaces.image witnessEdge := by
    simpa [subBoundary, witnessEdge, interiorEdgeSupport_ambientFaceBoundary_eq] using hcover
  have hwitness' : ∀ f ∈ peelFaces, witnessEdge f ∈ subBoundary f := by
    intro f hf
    rcases hparent f hf with ⟨p, hfp⟩
    simpa [subBoundary, witnessEdge, ambientFaceBoundary] using
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces hunique parentFace fallbackEdge hparentAdj hfp
  have hchildren' :
      ∀ f ∈ peelFaces, ∀ e ∈ (subBoundary f).erase (witnessEdge f),
        e ∈ selectedBoundarySupport subBoundary allFaces.attach allFaces.attach ∨
          ∃ g ∈ peelFaces, parentFace g = some f ∧ witnessEdge g = e := by
    intro f hf e he
    rcases hchildren f hf e (by simpa [subBoundary, witnessEdge, ambientFaceBoundary] using he) with
      hboundary | ⟨g, hg, hgf, hge⟩
    · left
      simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using hboundary
    · exact Or.inr ⟨g, hg, hgf, by simpa [witnessEdge] using hge⟩
  have hall' : ∀ e, totalIncidenceCount subBoundary allFaces.attach e ≤ 2 := by
    intro e
    simpa [subBoundary, totalIncidenceCount_ambientFaceBoundary_eq] using hall e
  have hzeroBoundary' :
      ∀ e ∈ selectedBoundarySupport subBoundary allFaces.attach allFaces.attach, z e = 0 := by
    intro e he
    exact hzeroBoundary e
      (by simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using he)
  have horth' :
      ∀ f ∈ peelFaces,
        ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
                (subBoundary f))
              z
              (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
                (subBoundary f)) = 0 := by
    intro f hf γ hγ0 hγd
    simpa [subBoundary, witnessEdge, ambientFaceBoundary] using horth f hf γ hγ0 hγd
  simpa [subBoundary, biUnion_attach_ambientFaceBoundary_eq] using
    zero_on_ambientFaceSupport_of_sortedHeightOrdered_parentFacePeelWitnessCover
      (C := C) (htait := htait) (z := z)
      (allFaces := allFaces.attach) (peelFaces := peelFaces) (faceBoundary := subBoundary)
      (parentFace := parentFace) (witnessEdge := witnessEdge) (height := height)
      hcover' hwitness' hchildren' hheight hall' hzeroBoundary' horth'

/-- Height-ordered primal-face-membership version of the interior-dual-spanning-forest route.
The local child condition is stated only in terms of primal face boundaries: every non-parent edge
of a peeled face is either boundary support or lies on a child face. Pairwise shared-edge
uniqueness then recovers the child's canonical parent-shared witness edge automatically. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_heightOrdered_parentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (height : AmbientFace allFaces → ℕ)
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ e ∈ faceBoundary g.1)
    (hheight : ∀ g ∈ peelFaces, ∀ f, parentFace g = some f → height f < height g)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  apply zero_on_ambientFaceSupport_of_interiorDualSpanningForest_heightOrdered_parentSharedEdgeWitnessCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces) (peelFaces := peelFaces)
    (faceBoundary := faceBoundary) (hunique := hunique) (parentFace := parentFace)
    (fallbackEdge := fallbackEdge) (height := height) (hparent := hparent)
    (hparentAdj := hparentAdj) (hcover := hcover) (hheight := hheight)
    (hall := hall) (hzeroBoundary := hzeroBoundary) (horth := horth)
  intro f hf e he
  rcases hchildren f hf e he with hboundary | ⟨g, hg, hgf, heg⟩
  · exact Or.inl hboundary
  · refine Or.inr ⟨g, hg, hgf, ?_⟩
    exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
      faceBoundary allFaces hunique parentFace fallbackEdge hparentAdj hall hgf heg
      ((Finset.mem_erase.1 he).2)

/-- Well-founded-parent specialization of the interior-dual-spanning-forest route. This removes the
explicit numeric height parameter from the parent-shared witness-edge interface: it is enough that
the parent relation on peeled faces is well founded. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_wellFounded_parentSharedEdgeWitnessCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hWF : WellFounded (ParentRel parentFace))
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧
          parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
            parentFace fallbackEdge hparentAdj g = e)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let subBoundary : AmbientFace allFaces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := allFaces) faceBoundary
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
      parentFace fallbackEdge hparentAdj
  have hcover' :
      interiorEdgeSupport subBoundary allFaces.attach ⊆ peelFaces.image witnessEdge := by
    simpa [subBoundary, witnessEdge, interiorEdgeSupport_ambientFaceBoundary_eq] using hcover
  have hwitness' : ∀ f ∈ peelFaces, witnessEdge f ∈ subBoundary f := by
    intro f hf
    rcases hparent f hf with ⟨p, hfp⟩
    simpa [subBoundary, witnessEdge, ambientFaceBoundary] using
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces hunique parentFace fallbackEdge hparentAdj hfp
  have hchildren' :
      ∀ f ∈ peelFaces, ∀ e ∈ (subBoundary f).erase (witnessEdge f),
        e ∈ selectedBoundarySupport subBoundary allFaces.attach allFaces.attach ∨
          ∃ g ∈ peelFaces, parentFace g = some f ∧ witnessEdge g = e := by
    intro f hf e he
    rcases hchildren f hf e (by simpa [subBoundary, witnessEdge, ambientFaceBoundary] using he) with
      hboundary | ⟨g, hg, hgf, hge⟩
    · left
      simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using hboundary
    · exact Or.inr ⟨g, hg, hgf, by simpa [witnessEdge] using hge⟩
  have hall' : ∀ e, totalIncidenceCount subBoundary allFaces.attach e ≤ 2 := by
    intro e
    simpa [subBoundary, totalIncidenceCount_ambientFaceBoundary_eq] using hall e
  have hzeroBoundary' :
      ∀ e ∈ selectedBoundarySupport subBoundary allFaces.attach allFaces.attach, z e = 0 := by
    intro e he
    exact hzeroBoundary e
      (by simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using he)
  have horth' :
      ∀ f ∈ peelFaces,
        ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
                (subBoundary f))
              z
              (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
                (subBoundary f)) = 0 := by
    intro f hf γ hγ0 hγd
    simpa [subBoundary, witnessEdge, ambientFaceBoundary] using horth f hf γ hγ0 hγd
  simpa [subBoundary, biUnion_attach_ambientFaceBoundary_eq] using
    zero_on_ambientFaceSupport_of_wellFounded_parentFacePeelWitnessCover
      (C := C) (htait := htait) (z := z)
      (allFaces := allFaces.attach) (peelFaces := peelFaces) (faceBoundary := subBoundary)
      (parentFace := parentFace) (witnessEdge := witnessEdge) (hWF := hWF)
      hcover' hwitness' hchildren' hall' hzeroBoundary' horth'

/-- Well-founded-parent and primal-face-membership version of the interior-dual-spanning-forest
route. This is the root-free analogue of the current paper-facing child-face wrapper. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_wellFounded_parentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hWF : WellFounded (ParentRel parentFace))
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ e ∈ faceBoundary g.1)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  apply zero_on_ambientFaceSupport_of_interiorDualSpanningForest_wellFounded_parentSharedEdgeWitnessCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces) (peelFaces := peelFaces)
    (faceBoundary := faceBoundary) (hunique := hunique) (parentFace := parentFace)
    (fallbackEdge := fallbackEdge) (hWF := hWF) (hparent := hparent)
    (hparentAdj := hparentAdj) (hcover := hcover)
    (hall := hall) (hzeroBoundary := hzeroBoundary) (horth := horth)
  intro f hf e he
  rcases hchildren f hf e he with hboundary | ⟨g, hg, hgf, heg⟩
  · exact Or.inl hboundary
  · refine Or.inr ⟨g, hg, hgf, ?_⟩
    exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
      faceBoundary allFaces hunique parentFace fallbackEdge hparentAdj hall hgf heg
      ((Finset.mem_erase.1 he).2)

/-- Root-free well-founded-parent data for the current interior-dual peeling route. This removes
the explicit numeric height from the geometric interface: it is enough to specify a parent relation
on peeled faces that is well founded, together with the child-face-membership cover condition. -/
structure InteriorDualWellFoundedParentPeelData {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) where
  peelFaces : Finset (AmbientFace allFaces)
  hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces
  parentFace : AmbientFace allFaces → Option (AmbientFace allFaces)
  fallbackEdge : AmbientFace allFaces → G.edgeSet
  hWF : WellFounded (ParentRel parentFace)
  hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p
  hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
    (interiorDualSpanningForest faceBoundary allFaces).Adj f p
  hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
    (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
      parentFace fallbackEdge hparentAdj)
  hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj f),
    e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
      ∃ g ∈ peelFaces, parentFace g = some f ∧ e ∈ faceBoundary g.1
  hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2

/-- Named constructor for the well-founded-parent interior-dual peeling data. -/
def interiorDualWellFoundedParentPeelDataOfWellFoundedParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hWF : WellFounded (ParentRel parentFace))
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ e ∈ faceBoundary g.1)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    InteriorDualWellFoundedParentPeelData allFaces faceBoundary :=
  { peelFaces := peelFaces
    hunique := hunique
    parentFace := parentFace
    fallbackEdge := fallbackEdge
    hWF := hWF
    hparent := hparent
    hparentAdj := hparentAdj
    hcover := hcover
    hchildren := hchildren
    hall := hall }

/-- The well-founded-parent interior-dual peeling data canonically yields a boundary-rooted peel
certificate on the ambient face subtype. -/
noncomputable def InteriorDualWellFoundedParentPeelData.toCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualWellFoundedParentPeelData allFaces faceBoundary) :
    CollarLayerFacePeelWitnessData allFaces.attach
      (ambientFaceBoundary (allFaces := allFaces) faceBoundary) := by
  let subBoundary : AmbientFace allFaces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := allFaces) faceBoundary
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
      data.parentFace data.fallbackEdge data.hparentAdj
  refine collarLayerFacePeelWitnessData_of_wellFounded_parentFacePeelWitnessCover
    allFaces.attach data.peelFaces subBoundary data.parentFace witnessEdge data.hWF ?_ ?_ ?_
  · simpa [subBoundary, witnessEdge, interiorEdgeSupport_ambientFaceBoundary_eq] using data.hcover
  · intro f hf
    rcases data.hparent f hf with ⟨p, hfp⟩
    simpa [subBoundary, witnessEdge, ambientFaceBoundary] using
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces data.hunique data.parentFace data.fallbackEdge data.hparentAdj hfp
  · intro f hf e he
    have he' : e ∈ (faceBoundary f.1).erase (witnessEdge f) := by
      simpa [subBoundary, witnessEdge, ambientFaceBoundary] using he
    have hef : e ∈ faceBoundary f.1 := (Finset.mem_erase.1 he').2
    rcases data.hchildren f hf e he' with hboundary | ⟨g, hg, hgf, heg⟩
    · exact Or.inl <| by
        simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using hboundary
    · refine Or.inr ⟨g, hg, hgf, ?_⟩
      exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
        faceBoundary allFaces data.hunique data.parentFace data.fallbackEdge data.hparentAdj
        data.hall hgf heg hef

/-- The weakest current root-free interior-dual package canonically upgrades to the weaker
explicit-remainder collar interface on attached ambient faces. This exposes the actual deeper
remainder after each collar without imposing the stronger global frontier-ownership condition. -/
noncomputable def
    InteriorDualWellFoundedParentPeelData.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualWellFoundedParentPeelData allFaces faceBoundary) :
    LocalRemainderBoundaryCollarLayerFacePeelWitnessData allFaces.attach
      (ambientFaceBoundary (allFaces := allFaces) faceBoundary) := by
  let collarData := data.toCollarLayerFacePeelWitnessData
  exact collarData.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    (hlayerSubset := by
      intro i f hf
      exact Finset.mem_attach _ _)
    (hall := by
      intro e
      simpa [ambientFaceBoundary, totalIncidenceCount_ambientFaceBoundary_eq] using data.hall e)

theorem
    InteriorDualWellFoundedParentPeelData.mem_peelFaces_of_mem_layer_toCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualWellFoundedParentPeelData allFaces faceBoundary)
    {i : Fin data.toCollarLayerFacePeelWitnessData.numLayers}
    {f : AmbientFace allFaces}
    (hf : f ∈ data.toCollarLayerFacePeelWitnessData.layerFaces i) :
    f ∈ data.peelFaces := by
  simpa [InteriorDualWellFoundedParentPeelData.toCollarLayerFacePeelWitnessData,
    collarLayerFacePeelWitnessData_of_wellFounded_parentFacePeelWitnessCover,
    collarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessCover]
    using (Finset.mem_filter.1 hf).1

theorem
    InteriorDualWellFoundedParentPeelData.mem_peelFaces_of_mem_layer_toLocalRemainderBoundaryCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualWellFoundedParentPeelData allFaces faceBoundary)
    {i : Fin data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData.numLayers}
    {f : AmbientFace allFaces}
    (hf : f ∈ data.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData.layerFaces i) :
    f ∈ data.peelFaces := by
  simpa [InteriorDualWellFoundedParentPeelData.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData,
    CollarLayerFacePeelWitnessData.toLocalRemainderBoundaryCollarLayerFacePeelWitnessData]
    using data.mem_peelFaces_of_mem_layer_toCollarLayerFacePeelWitnessData hf

/-- The well-founded-parent interior-dual peeling data canonically yields a boundary-rooted peel
certificate on the ambient face subtype. -/
noncomputable def InteriorDualWellFoundedParentPeelData.toBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualWellFoundedParentPeelData allFaces faceBoundary) :
    BoundaryRootedFacePeelCertificate allFaces.attach
      (ambientFaceBoundary (allFaces := allFaces) faceBoundary) := by
  let subBoundary : AmbientFace allFaces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := allFaces) faceBoundary
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
      data.parentFace data.fallbackEdge data.hparentAdj
  refine boundaryRootedFacePeelCertificate_of_wellFounded_parentFacePeelWitnessCover
    (allFaces := allFaces.attach) (peelFaces := data.peelFaces)
    (faceBoundary := subBoundary) (parentFace := data.parentFace)
    (witnessEdge := witnessEdge) data.hWF ?_ ?_ ?_
  · simpa [subBoundary, witnessEdge, interiorEdgeSupport_ambientFaceBoundary_eq] using data.hcover
  · intro f hf
    rcases data.hparent f hf with ⟨p, hfp⟩
    simpa [subBoundary, witnessEdge, ambientFaceBoundary] using
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces data.hunique data.parentFace data.fallbackEdge data.hparentAdj hfp
  · intro f hf e he
    have he' : e ∈ (faceBoundary f.1).erase (witnessEdge f) := by
      simpa [subBoundary, witnessEdge, ambientFaceBoundary] using he
    have hef : e ∈ faceBoundary f.1 := (Finset.mem_erase.1 he').2
    rcases data.hchildren f hf e he' with hboundary | ⟨g, hg, hgf, heg⟩
    · exact Or.inl <| by
        simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using hboundary
    · refine Or.inr ⟨g, hg, hgf, ?_⟩
      exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
        faceBoundary allFaces data.hunique data.parentFace data.fallbackEdge data.hparentAdj
        data.hall hgf heg hef

/-- Annihilator form of the packaged well-founded-parent interior-dual peeling data. -/
theorem zero_on_ambientFaceSupport_of_interiorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (data : InteriorDualWellFoundedParentPeelData allFaces faceBoundary)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
          data.parentFace data.fallbackEdge data.hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                  data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let subBoundary : AmbientFace allFaces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := allFaces) faceBoundary
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
      data.parentFace data.fallbackEdge data.hparentAdj
  have hcover' :
      interiorEdgeSupport subBoundary allFaces.attach ⊆ data.peelFaces.image witnessEdge := by
    simpa [subBoundary, witnessEdge, interiorEdgeSupport_ambientFaceBoundary_eq] using data.hcover
  have hwitness' : ∀ f ∈ data.peelFaces, witnessEdge f ∈ subBoundary f := by
    intro f hf
    rcases data.hparent f hf with ⟨p, hfp⟩
    simpa [subBoundary, witnessEdge, ambientFaceBoundary] using
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces data.hunique data.parentFace data.fallbackEdge data.hparentAdj hfp
  have hchildren' :
      ∀ f ∈ data.peelFaces, ∀ e ∈ (subBoundary f).erase (witnessEdge f),
        e ∈ selectedBoundarySupport subBoundary allFaces.attach allFaces.attach ∨
          ∃ g ∈ data.peelFaces, data.parentFace g = some f ∧ witnessEdge g = e := by
    intro f hf e he
    have he' : e ∈ (faceBoundary f.1).erase (witnessEdge f) := by
      simpa [subBoundary, witnessEdge, ambientFaceBoundary] using he
    have hef : e ∈ faceBoundary f.1 := (Finset.mem_erase.1 he').2
    rcases data.hchildren f hf e he' with hboundary | ⟨g, hg, hgf, heg⟩
    · exact Or.inl <| by
        simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using hboundary
    · refine Or.inr ⟨g, hg, hgf, ?_⟩
      exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
        faceBoundary allFaces data.hunique data.parentFace data.fallbackEdge data.hparentAdj
        data.hall hgf heg hef
  simpa [subBoundary, biUnion_attach_ambientFaceBoundary_eq] using
    zero_on_ambientFaceSupport_of_wellFounded_parentFacePeelWitnessCover
      (C := C) (htait := htait) (z := z)
      (allFaces := allFaces.attach) (peelFaces := data.peelFaces)
      (faceBoundary := subBoundary) (parentFace := data.parentFace)
      (witnessEdge := witnessEdge) data.hWF hcover' hwitness' hchildren'
      (hall := by
        intro e
        simpa [subBoundary, totalIncidenceCount_ambientFaceBoundary_eq] using data.hall e)
      (hzeroBoundary := by
        intro e he
        exact hzeroBoundary e <| by
          simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using he)
      (horth := by
        intro f hf γ hγ0 hγd
        simpa [subBoundary, witnessEdge, ambientFaceBoundary] using
          horth f hf γ hγ0 hγd)

/-- Root-distance version of the interior-dual-spanning-forest wrapper. This removes the explicit
`WellFounded` hypothesis from the parent-shared-edge interface: it is enough that parent edges
strictly decrease distance to some chosen root-label assignment. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_rootDistanceParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (rootFace : AmbientFace allFaces → AmbientFace allFaces)
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hdist : ∀ {g f : AmbientFace allFaces}, parentFace g = some f →
      (interiorDualSpanningForest faceBoundary allFaces).dist f (rootFace f) <
        (interiorDualSpanningForest faceBoundary allFaces).dist g (rootFace g))
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ e ∈ faceBoundary g.1)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_interiorDualSpanningForest_wellFounded_parentSharedEdgeFaceMembershipCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces) (peelFaces := peelFaces)
    (faceBoundary := faceBoundary) (hunique := hunique) (parentFace := parentFace)
    (fallbackEdge := fallbackEdge)
    (hWF := wellFounded_parentRel_of_rootDistance
      (interiorDualSpanningForest faceBoundary allFaces) parentFace rootFace
      (by
        intro g f hgf
        exact hdist hgf))
    (hparent := hparent) (hparentAdj := hparentAdj) (hcover := hcover)
    (hchildren := hchildren) (hall := hall) (hzeroBoundary := hzeroBoundary)
    (horth := horth)

/-- Root-face and primal-face-membership version of the interior-dual-spanning-forest wrapper.
This is the closest current interface to the paper's Step 2 wording: each peeled face has a parent
in the chosen forest, each face is assigned a root face in the ambient dual component containing
it, and every non-boundary/non-parent edge on a peeled face is only required to lie on a child face
at strictly greater forest-distance from the common root. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_adjInvariantRootedParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (rootFace : AmbientFace allFaces → AmbientFace allFaces)
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hreach : ∀ f ∈ peelFaces,
      (interiorDualGraph faceBoundary allFaces).Reachable f (rootFace f))
    (hrootAdj : ∀ ⦃f g : AmbientFace allFaces⦄,
      (interiorDualSpanningForest faceBoundary allFaces).Adj f g → rootFace f = rootFace g)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧
          e ∈ faceBoundary g.1 ∧
          (interiorDualSpanningForest faceBoundary allFaces).dist f (rootFace f) <
            (interiorDualSpanningForest faceBoundary allFaces).dist g (rootFace g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
      parentFace fallbackEdge hparentAdj
  apply zero_on_ambientFaceSupport_of_interiorDualSpanningForest_adjInvariantRootedAdjDistanceWitnessCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces) (peelFaces := peelFaces)
    (faceBoundary := faceBoundary) (rootFace := rootFace) (witnessEdge := witnessEdge)
  · simpa [witnessEdge] using hcover
  · exact hreach
  · exact hrootAdj
  · intro f hf
    rcases hparent f hf with ⟨p, hfp⟩
    simpa [witnessEdge] using
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces hunique parentFace fallbackEdge hparentAdj hfp
  · intro f hf e he
    rcases hchildren f hf e (by simpa [witnessEdge] using he) with
      hboundary | ⟨g, hg, hgf, heg, hlt⟩
    · exact Or.inl hboundary
    · refine Or.inr ⟨g, hg, (hparentAdj hgf).symm, ?_, hlt⟩
      exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
        faceBoundary allFaces hunique parentFace fallbackEdge hparentAdj hall hgf heg
        ((Finset.mem_erase.1 he).2)
  · exact hall
  · exact hzeroBoundary
  · intro f hf γ hγ0 hγd
    simpa [witnessEdge] using horth f hf γ hγ0 hγd

/-- Rooted-forest-orientation version of the current strongest interior-dual Step 2 wrapper.
Instead of requiring the chosen root face to be constant on every forest edge, it is enough to
specify a parent orientation of the forest and require root constancy only along parent edges. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_orientedRootedParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (rootFace : AmbientFace allFaces → AmbientFace allFaces)
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (horient : ∀ ⦃f g : AmbientFace allFaces⦄,
      (interiorDualSpanningForest faceBoundary allFaces).Adj f g →
        parentFace g = some f ∨ parentFace f = some g)
    (hreach : ∀ f ∈ peelFaces,
      (interiorDualGraph faceBoundary allFaces).Reachable f (rootFace f))
    (hrootParent : ∀ ⦃f g : AmbientFace allFaces⦄, parentFace g = some f → rootFace f = rootFace g)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧
          e ∈ faceBoundary g.1 ∧
          (interiorDualSpanningForest faceBoundary allFaces).dist f (rootFace f) <
            (interiorDualSpanningForest faceBoundary allFaces).dist g (rootFace g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                parentFace fallbackEdge hparentAdj f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  apply zero_on_ambientFaceSupport_of_interiorDualSpanningForest_adjInvariantRootedParentSharedEdgeFaceMembershipCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces)
    (peelFaces := peelFaces) (faceBoundary := faceBoundary)
    (hunique := hunique) (parentFace := parentFace) (fallbackEdge := fallbackEdge)
    (rootFace := rootFace) (hparent := hparent) (hparentAdj := hparentAdj)
    (hreach := hreach)
  · intro f g hadj
    exact eq_of_adj_of_parent_orientation
      (interiorDualSpanningForest faceBoundary allFaces) parentFace rootFace
      horient hrootParent hadj
  · exact hcover
  · exact hchildren
  · exact hall
  · exact hzeroBoundary
  · exact horth

/-- Canonical shortest-path-parent version of the current strongest interior-dual Step 2 wrapper.
This removes the explicit `parentFace` parameter: the parent relation is taken to be
`parentTowardsRoot` in the chosen interior-dual spanning forest, and witness edges are the
corresponding canonical shared interior edges. The remaining annulus-side burden is exactly the
root assignment and the child-face membership/distance condition. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_adjInvariantCanonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (rootFace : AmbientFace allFaces → AmbientFace allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hreach : ∀ f ∈ peelFaces,
      (interiorDualGraph faceBoundary allFaces).Reachable f (rootFace f))
    (hnotRoot : ∀ f ∈ peelFaces, f ≠ rootFace f)
    (hrootAdj : ∀ ⦃f g : AmbientFace allFaces⦄,
      (interiorDualSpanningForest faceBoundary allFaces).Adj f g → rootFace f = rootFace g)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique
        faceBoundary allFaces hunique rootFace fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique
          faceBoundary allFaces hunique rootFace fallbackEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest faceBoundary allFaces).Adj f g ∧
          e ∈ faceBoundary g.1 ∧
          (interiorDualSpanningForest faceBoundary allFaces).dist f (rootFace f) <
            (interiorDualSpanningForest faceBoundary allFaces).dist g (rootFace g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique
          faceBoundary allFaces hunique rootFace fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique
                faceBoundary allFaces hunique rootFace fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique
                faceBoundary allFaces hunique rootFace fallbackEdge f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique
                faceBoundary allFaces hunique rootFace fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique
                faceBoundary allFaces hunique rootFace fallbackEdge f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let T := interiorDualSpanningForest faceBoundary allFaces
  let parentFace : AmbientFace allFaces → Option (AmbientFace allFaces) :=
    parentTowardsRoot T rootFace
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique rootFace fallbackEdge
  have hreachT : ∀ f ∈ peelFaces, T.Reachable f (rootFace f) := by
    intro f hf
    simpa [T, interiorDualSpanningForest_reachable_eq faceBoundary allFaces] using hreach f hf
  have hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p := by
    intro f hf
    rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace)
        (u := f) (h := hreachT f hf) (hnotRoot f hf) with ⟨p, hp, _hadj, _hdist⟩
    exact ⟨p, hp⟩
  have hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p → T.Adj f p := by
    intro f p hfp
    exact parentTowardsRoot_some_adj T rootFace hfp
  apply zero_on_ambientFaceSupport_of_interiorDualSpanningForest_adjInvariantRootedParentSharedEdgeFaceMembershipCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces)
    (peelFaces := peelFaces) (faceBoundary := faceBoundary)
    (hunique := hunique) (parentFace := parentFace) (fallbackEdge := fallbackEdge)
    (rootFace := rootFace) (hparent := hparent) (hparentAdj := hparentAdj)
    (hreach := hreach)
  · exact hrootAdj
  · simpa [witnessEdge, rootedSharedInteriorEdgeOfPairwiseUnique, parentFace] using hcover
  · intro f hf e he
    rcases hchildren f hf e (by simpa [witnessEdge] using he) with
      hboundary | ⟨g, hg, hadj, heg, hlt⟩
    · exact Or.inl hboundary
    · refine Or.inr ⟨g, hg, ?_, heg, hlt⟩
      exact parentTowardsRoot_eq_some_of_adj_of_lt_dist_of_componentConstantRoot
        T (interiorDualSpanningForest_isAcyclic faceBoundary allFaces) rootFace hadj
        (hreachT f hf) (hreachT g hg) (hrootAdj hadj) hlt
  · exact hall
  · exact hzeroBoundary
  · intro f hf γ hγ0 hγd
    simpa [witnessEdge, rootedSharedInteriorEdgeOfPairwiseUnique, parentFace] using
      horth f hf γ hγ0 hγd

/-- Canonical root-set version of the strongest current interior-dual Step 2 wrapper. A finite
set of boundary roots covering and separating components determines the root assignment
`interiorDualSpanningForestRoot`; the shortest-path parent map and shared witness edges are then
chosen canonically in the selected interior-dual spanning forest. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedRoots_canonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelDisjoint : Disjoint peelFaces roots)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest faceBoundary allFaces).Adj f g ∧
          e ∈ faceBoundary g.1 ∧
          (interiorDualSpanningForest faceBoundary allFaces).dist
              f (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest faceBoundary allFaces).dist
              g (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let rootFace : AmbientFace allFaces → AmbientFace allFaces :=
    interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots
  apply zero_on_ambientFaceSupport_of_interiorDualSpanningForest_adjInvariantCanonicalRootedSharedEdgeFaceMembershipCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces)
    (peelFaces := peelFaces) (faceBoundary := faceBoundary)
    (hunique := hunique) (rootFace := rootFace) (fallbackEdge := fallbackEdge)
  · intro f hf
    simpa [rootFace, interiorDualSpanningForest_reachable_eq faceBoundary allFaces] using
      reachable_interiorDualSpanningForestRoot
        faceBoundary allFaces roots hcoverRoots hsepRoots f
  · intro f hf
    exact ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
      faceBoundary allFaces peelFaces roots hcoverRoots hsepRoots hpeelDisjoint hf
  · intro f g hadj
    simpa [rootFace] using
      interiorDualSpanningForestRoot_eq_of_adj
        faceBoundary allFaces roots hcoverRoots hsepRoots hadj
  · simpa [rootFace] using hcover
  · simpa [rootFace] using hchildren
  · exact hall
  · exact hzeroBoundary
  · simpa [rootFace] using horth

/-- Boundary-root version of the canonical root-set wrapper. Instead of supplying disjointness of
peeled faces and roots directly, it is enough to require that peeled faces avoid ambient boundary
edges while every designated root face meets the ambient boundary support. This matches the paper's
"rooted along the outer boundary" language more closely. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedBoundaryRoots_canonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest faceBoundary allFaces).Adj f g ∧
          e ∈ faceBoundary g.1 ∧
          (interiorDualSpanningForest faceBoundary allFaces).dist
              f (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest faceBoundary allFaces).dist
              g (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  apply zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedRoots_canonicalRootedSharedEdgeFaceMembershipCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces)
    (peelFaces := peelFaces) (roots := roots) (faceBoundary := faceBoundary)
    (hunique := hunique) (fallbackEdge := fallbackEdge)
    (hcoverRoots := hcoverRoots) (hsepRoots := hsepRoots)
    (hpeelDisjoint := disjoint_peelFaces_roots_of_boundarySeparation
      faceBoundary allFaces peelFaces roots hpeelInterior hrootsBoundary)
    (hcover := hcover) (hchildren := hchildren) (hall := hall)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Boundary-subset version of the canonical rooted wrapper. The designated roots are required to
meet a chosen subset of the ambient boundary support, rather than merely some ambient boundary
edge. This is the direct form needed for annulus arguments rooted specifically along the outer
boundary. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedBoundarySubsetRoots_canonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (boundarySupport : Finset G.edgeSet)
    (hboundarySupport : boundarySupport ⊆
      selectedBoundarySupport faceBoundary allFaces allFaces)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ boundarySupport)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest faceBoundary allFaces).Adj f g ∧
          e ∈ faceBoundary g.1 ∧
          (interiorDualSpanningForest faceBoundary allFaces).dist
              f (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest faceBoundary allFaces).dist
              g (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  apply zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedBoundaryRoots_canonicalRootedSharedEdgeFaceMembershipCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces)
    (peelFaces := peelFaces) (roots := roots) (faceBoundary := faceBoundary)
    (hunique := hunique) (fallbackEdge := fallbackEdge)
    (hcoverRoots := hcoverRoots) (hsepRoots := hsepRoots)
    (hpeelInterior := hpeelInterior)
    (hrootsBoundary := by
      intro r hr
      rcases hrootsBoundary r hr with ⟨e, her, heB⟩
      exact ⟨e, her, hboundarySupport heB⟩)
    (hcover := hcover) (hchildren := hchildren) (hall := hall)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Canonical parent-relation version of the boundary-root wrapper. This removes the explicit
root-distance inequality from the current strongest canonical interface: once the annulus geometry
identifies actual child faces in the canonical `parentTowardsRoot` relation, the required distance
growth follows automatically from shortest-path geometry in the chosen interior-dual spanning
forest. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedBoundaryRoots_canonicalParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces)
              (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots) g = some f ∧
          e ∈ faceBoundary g.1)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let T := interiorDualSpanningForest faceBoundary allFaces
  let rootFace : AmbientFace allFaces → AmbientFace allFaces :=
    interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots
  apply zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedBoundaryRoots_canonicalRootedSharedEdgeFaceMembershipCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces)
    (peelFaces := peelFaces) (roots := roots) (faceBoundary := faceBoundary)
    (hunique := hunique) (fallbackEdge := fallbackEdge)
    (hcoverRoots := hcoverRoots) (hsepRoots := hsepRoots)
    (hpeelInterior := hpeelInterior) (hrootsBoundary := hrootsBoundary)
    (hcover := hcover) (hall := hall) (hzeroBoundary := hzeroBoundary) (horth := horth)
  intro f hf e he
  rcases hchildren f hf e he with hboundary | ⟨g, hg, hgf, heg⟩
  · exact Or.inl hboundary
  · refine Or.inr ⟨g, hg, (parentTowardsRoot_some_adj T rootFace hgf).symm, heg, ?_⟩
    have hneq : g ≠ rootFace g := by
      intro hgr
      rw [parentTowardsRoot_eq_none_of_eq_root (T := T) (root := rootFace) hgr] at hgf
      simp at hgf
    rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace)
        (u := g)
        (h := reachable_interiorDualSpanningForestRoot
          faceBoundary allFaces roots hcoverRoots hsepRoots g)
        hneq with ⟨w, hw, _hadj, hdist⟩
    rw [hgf] at hw
    injection hw with hwf
    subst w
    have hroot :
        rootFace f = rootFace g := by
      exact interiorDualSpanningForestRoot_eq_of_adj
        faceBoundary allFaces roots hcoverRoots hsepRoots
        (parentTowardsRoot_some_adj T rootFace hgf).symm
    calc
      T.dist f (rootFace f) = T.dist f (rootFace g) := by rw [hroot]
      _ < T.dist f (rootFace g) + 1 := Nat.lt_succ_self _
      _ = T.dist g (rootFace g) := by rw [hdist]

/-- Boundary-subset version of the canonical parent wrapper. This lets the annulus side state the
current strongest parent-equality route with roots meeting a distinguished outer boundary support
instead of an arbitrary ambient boundary edge. -/
theorem zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedBoundarySubsetRoots_canonicalParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (boundarySupport : Finset G.edgeSet)
    (hboundarySupport : boundarySupport ⊆
      selectedBoundarySupport faceBoundary allFaces allFaces)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ boundarySupport)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces)
              (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots) g = some f ∧
          e ∈ faceBoundary g.1)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
                fallbackEdge f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  apply zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedBoundaryRoots_canonicalParentSharedEdgeFaceMembershipCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces)
    (peelFaces := peelFaces) (roots := roots) (faceBoundary := faceBoundary)
    (hunique := hunique) (fallbackEdge := fallbackEdge)
    (hcoverRoots := hcoverRoots) (hsepRoots := hsepRoots)
    (hpeelInterior := hpeelInterior)
    (hrootsBoundary := by
      intro r hr
      rcases hrootsBoundary r hr with ⟨e, her, heB⟩
      exact ⟨e, her, hboundarySupport heB⟩)
    (hcover := hcover) (hchildren := hchildren) (hall := hall)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

theorem rootedSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
    {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (rootFace : AmbientFace allFaces → AmbientFace allFaces)
    (fallbackEdge : AmbientFace allFaces → E)
    {g f : AmbientFace allFaces}
    (hgf : parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces) rootFace g = some f) :
    rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        rootFace fallbackEdge g ∈ faceBoundary g.1 := by
  exact parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
    faceBoundary allFaces hunique
    (parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces) rootFace)
    fallbackEdge
    (by
      intro u v huv
      exact parentTowardsRoot_some_adj
        (interiorDualSpanningForest faceBoundary allFaces) rootFace huv)
    hgf

theorem rootedSharedInteriorEdgeOfPairwiseUnique_mem_parent_faceBoundary
    {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (rootFace : AmbientFace allFaces → AmbientFace allFaces)
    (fallbackEdge : AmbientFace allFaces → E)
    {g f : AmbientFace allFaces}
    (hgf : parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces) rootFace g = some f) :
    rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        rootFace fallbackEdge g ∈ faceBoundary f.1 := by
  exact parentSharedInteriorEdgeOfPairwiseUnique_mem_parent_faceBoundary
    faceBoundary allFaces hunique
    (parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces) rootFace)
    fallbackEdge
    (by
      intro u v huv
      exact parentTowardsRoot_some_adj
        (interiorDualSpanningForest faceBoundary allFaces) rootFace huv)
    hgf

theorem rootedSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
    {E : Type*} [DecidableEq E]
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (rootFace : AmbientFace allFaces → AmbientFace allFaces)
    (fallbackEdge : AmbientFace allFaces → E)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2)
    {g f : AmbientFace allFaces}
    (hgf : parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces) rootFace g = some f)
    {e : E} (heg : e ∈ faceBoundary g.1) (hef : e ∈ faceBoundary f.1) :
    rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        rootFace fallbackEdge g = e := by
  exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
    faceBoundary allFaces hunique
    (parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces) rootFace)
    fallbackEdge
    (by
      intro u v huv
      exact parentTowardsRoot_some_adj
        (interiorDualSpanningForest faceBoundary allFaces) rootFace huv)
    hall hgf heg hef

/-- Nondegenerate canonical-parent cover witness.  If an actual interior edge is covered by the
rooted shared-edge map, then the covering face is a peeled non-root face with a real shortest-path
parent, and its rooted shared edge is exactly the given interior edge.  In particular the cover of
an interior edge cannot be witnessed by the fallback branch of
`rootedSharedInteriorEdgeOfPairwiseUnique`. -/
theorem exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_canonicalParentCover_of_mem_interiorEdgeSupport
    {G : SimpleGraph V}
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport faceBoundary allFaces) :
    ∃ f ∈ peelFaces,
      f ≠ interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f ∧
      (∃ p,
        parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces)
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots) f =
            some p) ∧
      rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f = e ∧
      e ∈ faceBoundary f.1 := by
  let T := interiorDualSpanningForest faceBoundary allFaces
  let rootFace : AmbientFace allFaces → AmbientFace allFaces :=
    interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots
  rcases Finset.mem_image.1 (hcover he) with ⟨f, hfPeel, hfe⟩
  have hdisj : Disjoint peelFaces roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      faceBoundary allFaces peelFaces roots hpeelInterior hrootsBoundary
  have hneq : f ≠ rootFace f := by
    simpa [rootFace] using
      ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
        faceBoundary allFaces peelFaces roots hcoverRoots hsepRoots hdisj hfPeel
  rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := f)
      (h := reachable_interiorDualSpanningForestRoot
        faceBoundary allFaces roots hcoverRoots hsepRoots f)
      hneq with ⟨p, hfp, _hadj, _hdist⟩
  have hfWitness :
      rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          rootFace fallbackEdge f ∈ faceBoundary f.1 := by
    exact rootedSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
      faceBoundary allFaces hunique rootFace fallbackEdge hfp
  refine ⟨f, hfPeel, ?_, ?_, ?_, ?_⟩
  · simpa [rootFace] using hneq
  · exact ⟨p, by simpa [T, rootFace] using hfp⟩
  · simpa [rootFace] using hfe
  · rw [← hfe]
    simpa [rootFace] using hfWitness

/-- Nonempty-support form of
`exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_canonicalParentCover_of_mem_interiorEdgeSupport`.
It makes the nondegenerate branch of the canonical-parent constructor explicit: a nonempty
interior-edge support produces an actual peeled non-root parent witness. -/
theorem exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_canonicalParentCover_of_interiorEdgeSupport_nonempty
    {G : SimpleGraph V}
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hInterior : (interiorEdgeSupport faceBoundary allFaces).Nonempty) :
    ∃ e ∈ interiorEdgeSupport faceBoundary allFaces,
      ∃ f ∈ peelFaces,
        f ≠ interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f ∧
        (∃ p,
          parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces)
            (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots) f =
              some p) ∧
        rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
            (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
            fallbackEdge f = e ∧
        e ∈ faceBoundary f.1 := by
  rcases hInterior with ⟨e, he⟩
  rcases exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_canonicalParentCover_of_mem_interiorEdgeSupport
      faceBoundary allFaces peelFaces roots hunique fallbackEdge hcoverRoots hsepRoots
      hpeelInterior hrootsBoundary hcover he with
    ⟨f, hfPeel, hfNonroot, hfParent, hfe, hef⟩
  exact ⟨e, he, f, hfPeel, hfNonroot, hfParent, hfe, hef⟩

/-- The canonical parent child-membership condition follows from the same raw shared-edge cover,
provided ambient edge incidences are at most two.  A non-witness edge on a peeled face is either
already selected boundary support, or it is an interior edge; the cover then gives a peeled child
whose canonical parent is forced back to the original face by the two-incidence bound. -/
theorem canonicalParentChildMembership_of_canonicalParentCover
    {G : SimpleGraph V}
    (faceBoundary : F → Finset G.edgeSet) (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces)
              (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots) g =
                some f ∧
          e ∈ faceBoundary g.1 := by
  intro f hfPeel e heErase
  let T := interiorDualSpanningForest faceBoundary allFaces
  let rootFace : AmbientFace allFaces → AmbientFace allFaces :=
    interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots
  let witness : AmbientFace allFaces → G.edgeSet :=
    rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique rootFace fallbackEdge
  by_cases hboundary : e ∈ selectedBoundarySupport faceBoundary allFaces allFaces
  · exact Or.inl hboundary
  · have hef : e ∈ faceBoundary f.1 := (Finset.mem_erase.1 heErase).2
    have hneWitness : e ≠ witness f := by
      simpa [witness, rootFace] using (Finset.mem_erase.1 heErase).1
    have heInterior : e ∈ interiorEdgeSupport faceBoundary allFaces := by
      have heUnion : e ∈ allFaces.biUnion faceBoundary :=
        Finset.mem_biUnion.2 ⟨f.1, f.2, hef⟩
      have heSplit :
          e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∪
            interiorEdgeSupport faceBoundary allFaces := by
        rw [← biUnion_eq_selectedBoundarySupport_union_interiorEdgeSupport_of_totalIncidenceCount_le_two
          faceBoundary allFaces hall]
        exact heUnion
      rcases Finset.mem_union.1 heSplit with heBoundary | heInterior
      · exact False.elim (hboundary heBoundary)
      · exact heInterior
    rcases
        exists_nonroot_peelFace_parent_rootedSharedInteriorEdge_eq_of_canonicalParentCover_of_mem_interiorEdgeSupport
          faceBoundary allFaces peelFaces roots hunique fallbackEdge hcoverRoots hsepRoots
          hpeelInterior hrootsBoundary hcover heInterior with
      ⟨g, hgPeel, _hgNonroot, ⟨p, hgp⟩, hge, heg⟩
    have hgp' : parentTowardsRoot T rootFace g = some p := by
      simpa [T, rootFace] using hgp
    have hep : e ∈ faceBoundary p.1 := by
      rw [← hge]
      simpa [rootFace] using
        rootedSharedInteriorEdgeOfPairwiseUnique_mem_parent_faceBoundary
          faceBoundary allFaces hunique rootFace fallbackEdge hgp'
    have hgpNe : g.1 ≠ p.1 := by
      have hadj : (interiorDualSpanningForest faceBoundary allFaces).Adj g p := by
        exact parentTowardsRoot_some_adj
          (interiorDualSpanningForest faceBoundary allFaces) rootFace hgp'
      exact (interiorDualGraph_adj_iff faceBoundary allFaces).1
        (interiorDualSpanningForest_le faceBoundary allFaces hadj) |>.1
    rcases eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        faceBoundary allFaces hall g.2 p.2 f.2 hgpNe heg hep hef with
      hfEqG | hfEqP
    · have hgf : g = f := Subtype.ext hfEqG.symm
      have hwitness : witness f = e := by
        rw [← hgf]
        simpa [witness, rootFace] using hge
      exact False.elim (hneWitness hwitness.symm)
    · have hpf : p = f := Subtype.ext hfEqP.symm
      refine Or.inr ⟨g, hgPeel, ?_, heg⟩
      simpa [rootFace, hpf] using hgp

/-- Certificate-packaged form of the current strongest canonical boundary-root interior-dual
wrapper. The annulus side can now aim directly at a `BoundaryRootedFacePeelCertificate` on the
ambient face subtype by supplying the boundary-root cover/separation data and the canonical
parent-child face-membership condition. -/
noncomputable def
    boundaryRootedFacePeelCertificate_of_interiorDualSpanningForest_coverSeparatedBoundaryRoots_canonicalParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces)
              (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots) g = some f ∧
          e ∈ faceBoundary g.1)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    BoundaryRootedFacePeelCertificate allFaces.attach
      (ambientFaceBoundary (allFaces := allFaces) faceBoundary) := by
  let T := interiorDualSpanningForest faceBoundary allFaces
  let rootFace : AmbientFace allFaces → AmbientFace allFaces :=
    interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots
  let parentFace : AmbientFace allFaces → Option (AmbientFace allFaces) :=
    parentTowardsRoot T rootFace
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique rootFace fallbackEdge
  let height : AmbientFace allFaces → ℕ := fun f => T.dist f (rootFace f)
  have hdisj : Disjoint peelFaces roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      faceBoundary allFaces peelFaces roots hpeelInterior hrootsBoundary
  refine boundaryRootedFacePeelCertificate_of_sortedHeightOrdered_parentFacePeelWitnessCover
    (allFaces := allFaces.attach) (peelFaces := peelFaces)
    (faceBoundary := ambientFaceBoundary (allFaces := allFaces) faceBoundary)
    (parentFace := parentFace) (witnessEdge := witnessEdge) (height := height)
    ?_ ?_ ?_ ?_
  · intro e he
    have he' : e ∈ interiorEdgeSupport faceBoundary allFaces := by
      simpa [interiorEdgeSupport_ambientFaceBoundary_eq (faceBoundary := faceBoundary)
        (allFaces := allFaces)] using he
    simpa [witnessEdge, rootFace] using hcover he'
  · intro f hf
    have hneq : f ≠ rootFace f :=
      ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
        faceBoundary allFaces peelFaces roots hcoverRoots hsepRoots hdisj hf
    rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := f)
        (h := reachable_interiorDualSpanningForestRoot
          faceBoundary allFaces roots hcoverRoots hsepRoots f)
        hneq with ⟨p, hfp, _hadj, _hdist⟩
    simpa [ambientFaceBoundary, witnessEdge, rootFace] using
      rootedSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces hunique rootFace fallbackEdge hfp
  · intro f hf e he
    have he' : e ∈ (faceBoundary f.1).erase (witnessEdge f) := by
      simpa [ambientFaceBoundary, witnessEdge] using he
    have hef : e ∈ faceBoundary f.1 := (Finset.mem_erase.1 he').2
    rcases hchildren f hf e he' with hboundary | ⟨g, hg, hgf, heg⟩
    · exact Or.inl <| by
        simpa [selectedBoundarySupport_ambientFaceBoundary_eq (faceBoundary := faceBoundary)
          (allFaces := allFaces)] using hboundary
    · refine Or.inr ⟨g, hg, hgf, ?_⟩
      exact rootedSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
        faceBoundary allFaces hunique rootFace fallbackEdge hall hgf heg hef
  · intro g hg f hgf
    have hgf' : parentTowardsRoot T rootFace g = some f := by
      simpa [parentFace] using hgf
    have hneq : g ≠ rootFace g :=
      ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
        faceBoundary allFaces peelFaces roots hcoverRoots hsepRoots hdisj hg
    rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := g)
        (h := reachable_interiorDualSpanningForestRoot
          faceBoundary allFaces roots hcoverRoots hsepRoots g)
        hneq with ⟨w, hw, _hadj, hdist⟩
    rw [hgf'] at hw
    injection hw with hwf
    subst w
    have hroot : rootFace f = rootFace g := by
      exact interiorDualSpanningForestRoot_eq_of_adj
        faceBoundary allFaces roots hcoverRoots hsepRoots
        (parentTowardsRoot_some_adj T rootFace hgf').symm
    dsimp [height]
    calc
      T.dist f (rootFace f) = T.dist f (rootFace g) := by rw [hroot]
      _ < T.dist f (rootFace g) + 1 := Nat.lt_succ_self _
      _ = T.dist g (rootFace g) := by rw [hdist]

/-- Geometric data for the current strongest boundary-rooted interior-dual peeling route. This is
the natural target for the remaining annulus theorem: once such data is constructed, the
certificate and annihilator layers are already available downstream. -/
structure InteriorDualBoundaryRootParentPeelData {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) where
  peelFaces : Finset (AmbientFace allFaces)
  roots : Finset (AmbientFace allFaces)
  hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces
  fallbackEdge : AmbientFace allFaces → G.edgeSet
  hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots
  hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots
  hpeelInterior : ∀ f ∈ peelFaces,
    Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces)
  hrootsBoundary : ∀ r ∈ roots,
    ∃ e ∈ faceBoundary r.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces
  hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
    (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
      (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
      fallbackEdge)
  hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge f),
    e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
      ∃ g ∈ peelFaces,
        parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces)
            (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots) g = some f ∧
        e ∈ faceBoundary g.1
  hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2

theorem InteriorDualBoundaryRootParentPeelData.mem_roots_of_not_mem_peelFaces
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootParentPeelData allFaces faceBoundary)
    {f : AmbientFace allFaces} (hfPeel : f ∉ data.peelFaces) :
    f ∈ data.roots := by
  let T := interiorDualSpanningForest faceBoundary allFaces
  let rootFace : AmbientFace allFaces → AmbientFace allFaces :=
    interiorDualSpanningForestRoot faceBoundary allFaces data.roots
      data.hcoverRoots data.hsepRoots
  by_contra hfRoot
  have hfNeRootFace : f ≠ rootFace f := by
    intro hEq
    exact hfRoot (hEq ▸
      interiorDualSpanningForestRoot_mem_roots
        faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots f)
  rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace)
      (u := f)
      (h := reachable_interiorDualSpanningForestRoot
        faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots f)
      hfNeRootFace with
    ⟨p, hfp, hadjfp, hdistfp⟩
  let e :=
    sharedInteriorEdgeOfAdjOfPairwiseUnique faceBoundary allFaces data.hunique
      (interiorDualSpanningForest_le faceBoundary allFaces hadjfp)
  have hef : e ∈ faceBoundary f.1 := by
    exact
      sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_left
        faceBoundary allFaces data.hunique
        (interiorDualSpanningForest_le faceBoundary allFaces hadjfp)
  have hep : e ∈ faceBoundary p.1 := by
    exact
      sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
        faceBoundary allFaces data.hunique
        (interiorDualSpanningForest_le faceBoundary allFaces hadjfp)
  have heInt : e ∈ interiorEdgeSupport faceBoundary allFaces := by
    exact
      (mem_sharedInteriorEdges_iff faceBoundary allFaces).1
        (sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
          faceBoundary allFaces data.hunique
          (interiorDualSpanningForest_le faceBoundary allFaces hadjfp)) |>.1
  rcases Finset.mem_image.1 (data.hcover heInt) with ⟨g, hgPeel, hge⟩
  have hdisj : Disjoint data.peelFaces data.roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      faceBoundary allFaces data.peelFaces data.roots
      data.hpeelInterior data.hrootsBoundary
  have hgNeRootFace : g ≠ rootFace g :=
    ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
      faceBoundary allFaces data.peelFaces data.roots
      data.hcoverRoots data.hsepRoots hdisj hgPeel
  rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace)
      (u := g)
      (h := reachable_interiorDualSpanningForestRoot
        faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots g)
      hgNeRootFace with
    ⟨q, hgq, hadjgq, hdistgq⟩
  have heg : e ∈ faceBoundary g.1 := by
    rw [← hge]
    exact
      rootedSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces data.hunique rootFace data.fallbackEdge hgq
  have heq : e ∈ faceBoundary q.1 := by
    let e' :=
      sharedInteriorEdgeOfAdjOfPairwiseUnique faceBoundary allFaces data.hunique
        (interiorDualSpanningForest_le faceBoundary allFaces hadjgq)
    have he'g : e' ∈ faceBoundary g.1 := by
      exact
        sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_left
          faceBoundary allFaces data.hunique
          (interiorDualSpanningForest_le faceBoundary allFaces hadjgq)
    have he'q : e' ∈ faceBoundary q.1 := by
      exact
        sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
          faceBoundary allFaces data.hunique
          (interiorDualSpanningForest_le faceBoundary allFaces hadjgq)
    have heq' :
        rootedSharedInteriorEdgeOfPairwiseUnique
            faceBoundary allFaces data.hunique rootFace data.fallbackEdge g = e' := by
      exact
        rootedSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
          faceBoundary allFaces data.hunique rootFace data.fallbackEdge data.hall
          hgq he'g he'q
    rw [← hge, heq']
    exact he'q
  have hfpNe : f.1 ≠ p.1 := by
    exact (interiorDualGraph_adj_iff faceBoundary allFaces).1
      (interiorDualSpanningForest_le faceBoundary allFaces hadjfp) |>.1
  have hgEq : g = p := by
    rcases eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        faceBoundary allFaces data.hall f.2 p.2 g.2 hfpNe hef hep heg with
      hgEq | hgEq
    · exact False.elim (hfPeel (Subtype.ext hgEq ▸ hgPeel))
    · exact Subtype.ext hgEq
  subst g
  have hpqNe : p.1 ≠ q.1 := by
    exact (interiorDualGraph_adj_iff faceBoundary allFaces).1
      (interiorDualSpanningForest_le faceBoundary allFaces hadjgq) |>.1
  have hqEq : q = f := by
    rcases eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        faceBoundary allFaces data.hall f.2 p.2 q.2 hfpNe hef hep heq with
      hqEq | hqEq
    · exact Subtype.ext hqEq
    · exact False.elim (hpqNe hqEq.symm)
  subst q
  have hrootEq : rootFace p = rootFace f := by
    simpa [rootFace] using
      interiorDualSpanningForestRoot_eq_of_adj
        faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots hadjfp |>.symm
  rw [hrootEq] at hdistgq
  have hdistfp' : T.dist p (rootFace f) + 1 = T.dist f (rootFace f) := by
    simpa [T, rootFace] using hdistfp
  omega

theorem InteriorDualBoundaryRootParentPeelData.exists_mem_selectedBoundarySupport_of_not_mem_peelFaces
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootParentPeelData allFaces faceBoundary)
    {f : AmbientFace allFaces} (hfPeel : f ∉ data.peelFaces) :
    ∃ e ∈ faceBoundary f.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces := by
  exact data.hrootsBoundary f (data.mem_roots_of_not_mem_peelFaces hfPeel)

/-- Named constructor for the strongest current boundary-root interior-dual peeling data. This is
the structure-level version of the long theorem hypotheses, intended as the direct target for the
remaining annulus-side geometry. -/
def interiorDualBoundaryRootParentPeelDataOfCoverSeparatedBoundaryRootsCanonicalParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces)
              (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots) g = some f ∧
          e ∈ faceBoundary g.1)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    InteriorDualBoundaryRootParentPeelData allFaces faceBoundary :=
  { peelFaces := peelFaces
    roots := roots
    hunique := hunique
    fallbackEdge := fallbackEdge
    hcoverRoots := hcoverRoots
    hsepRoots := hsepRoots
    hpeelInterior := hpeelInterior
    hrootsBoundary := hrootsBoundary
    hcover := hcover
    hchildren := hchildren
    hall := hall }

/-- Canonical-parent constructor for boundary-root interior-dual peeling data from the raw
shared-edge cover.  The child-membership hypothesis is not an independent input: it follows from
the cover and the ambient two-incidence bound. -/
def interiorDualBoundaryRootParentPeelDataOfCoverSeparatedBoundaryRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V}
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    InteriorDualBoundaryRootParentPeelData allFaces faceBoundary :=
  interiorDualBoundaryRootParentPeelDataOfCoverSeparatedBoundaryRootsCanonicalParentSharedEdgeFaceMembershipCover
    (allFaces := allFaces) (peelFaces := peelFaces) (roots := roots)
    (faceBoundary := faceBoundary) hunique fallbackEdge hcoverRoots hsepRoots
    hpeelInterior hrootsBoundary hcover
    (canonicalParentChildMembership_of_canonicalParentCover
      faceBoundary allFaces peelFaces roots hunique fallbackEdge hcoverRoots hsepRoots
      hpeelInterior hrootsBoundary hcover hall)
    hall

/-- Boundary-subset version of the strongest current boundary-root package constructor. This lets
the annulus side package roots meeting a designated outer boundary support while still landing in
the existing boundary-root parent structure. -/
def interiorDualBoundaryRootParentPeelDataOfCoverSeparatedBoundarySubsetRootsCanonicalParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (boundarySupport : Finset G.edgeSet)
    (hboundarySupport : boundarySupport ⊆
      selectedBoundarySupport faceBoundary allFaces allFaces)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ boundarySupport)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest faceBoundary allFaces)
              (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots) g = some f ∧
          e ∈ faceBoundary g.1)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    InteriorDualBoundaryRootParentPeelData allFaces faceBoundary :=
  interiorDualBoundaryRootParentPeelDataOfCoverSeparatedBoundaryRootsCanonicalParentSharedEdgeFaceMembershipCover
    (allFaces := allFaces) (peelFaces := peelFaces) (roots := roots)
    (faceBoundary := faceBoundary) hunique fallbackEdge hcoverRoots hsepRoots
    hpeelInterior
    (by
      intro r hr
      rcases hrootsBoundary r hr with ⟨e, her, heB⟩
      exact ⟨e, her, hboundarySupport heB⟩)
    hcover hchildren hall

/-- The strongest current interior-dual geometric data canonically induces a boundary-rooted peel
certificate on the ambient face subtype. -/
noncomputable def InteriorDualBoundaryRootParentPeelData.toBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootParentPeelData allFaces faceBoundary) :
    BoundaryRootedFacePeelCertificate allFaces.attach
      (ambientFaceBoundary (allFaces := allFaces) faceBoundary) :=
  boundaryRootedFacePeelCertificate_of_interiorDualSpanningForest_coverSeparatedBoundaryRoots_canonicalParentSharedEdgeFaceMembershipCover
    allFaces data.peelFaces data.roots faceBoundary data.hunique data.fallbackEdge
    data.hcoverRoots data.hsepRoots data.hpeelInterior data.hrootsBoundary
    data.hcover data.hchildren data.hall

/-- Annihilator form of the packaged strongest interior-dual boundary-root geometry. -/
theorem zero_on_ambientFaceSupport_of_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (data : InteriorDualBoundaryRootParentPeelData allFaces faceBoundary)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces data.roots
            data.hcoverRoots data.hsepRoots)
          data.fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_interiorDualSpanningForest_coverSeparatedBoundaryRoots_canonicalParentSharedEdgeFaceMembershipCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces)
    (peelFaces := data.peelFaces) (roots := data.roots) (faceBoundary := faceBoundary)
    (hunique := data.hunique) (fallbackEdge := data.fallbackEdge)
    (hcoverRoots := data.hcoverRoots) (hsepRoots := data.hsepRoots)
    (hpeelInterior := data.hpeelInterior) (hrootsBoundary := data.hrootsBoundary)
    (hcover := data.hcover) (hchildren := data.hchildren) (hall := data.hall)
    (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Geometric data for the weaker boundary-root adjacency-distance branch of the interior-dual
peeling route. This matches the annulus output before identifying each child with the canonical
shortest-path parent: every non-witness edge on a peeled face lies either on the ambient boundary
or on an adjacent peeled face at strictly greater boundary-root distance. -/
structure InteriorDualBoundaryRootAdjDistancePeelData {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) where
  peelFaces : Finset (AmbientFace allFaces)
  roots : Finset (AmbientFace allFaces)
  hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces
  fallbackEdge : AmbientFace allFaces → G.edgeSet
  hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots
  hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots
  hpeelInterior : ∀ f ∈ peelFaces,
    Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces)
  hrootsBoundary : ∀ r ∈ roots,
    ∃ e ∈ faceBoundary r.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces
  hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
    (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
      (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
      fallbackEdge)
  hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge f),
    e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
      ∃ g ∈ peelFaces,
        (interiorDualSpanningForest faceBoundary allFaces).Adj f g ∧
        e ∈ faceBoundary g.1 ∧
        (interiorDualSpanningForest faceBoundary allFaces).dist
            f (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f) <
          (interiorDualSpanningForest faceBoundary allFaces).dist
            g (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots g)
  hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2

/-- Named constructor for the weaker boundary-root adjacency-distance package. -/
def interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest faceBoundary allFaces).Adj f g ∧
          e ∈ faceBoundary g.1 ∧
          (interiorDualSpanningForest faceBoundary allFaces).dist
              f (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest faceBoundary allFaces).dist
              g (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    InteriorDualBoundaryRootAdjDistancePeelData allFaces faceBoundary :=
  { peelFaces := peelFaces
    roots := roots
    hunique := hunique
    fallbackEdge := fallbackEdge
    hcoverRoots := hcoverRoots
    hsepRoots := hsepRoots
    hpeelInterior := hpeelInterior
    hrootsBoundary := hrootsBoundary
    hcover := hcover
    hchildren := hchildren
    hall := hall }

/-- Boundary-subset version of the weaker boundary-root adjacency-distance package constructor.
This lets the annulus side package roots meeting a designated outer boundary support while still
landing in the existing boundary-root adjacency-distance structure. -/
def interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundarySubsetRootsCanonicalRootedSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (allFaces : Finset F)
    (peelFaces roots : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (boundarySupport : Finset G.edgeSet)
    (hboundarySupport : boundarySupport ⊆
      selectedBoundarySupport faceBoundary allFaces allFaces)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (hcoverRoots : RootSetCovers (interiorDualGraph faceBoundary allFaces) roots)
    (hsepRoots : RootSetSeparated (interiorDualGraph faceBoundary allFaces) roots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (faceBoundary f.1) (selectedBoundarySupport faceBoundary allFaces allFaces))
    (hrootsBoundary : ∀ r ∈ roots,
      ∃ e ∈ faceBoundary r.1, e ∈ boundarySupport)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
        fallbackEdge))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots)
          fallbackEdge f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces,
          (interiorDualSpanningForest faceBoundary allFaces).Adj f g ∧
          e ∈ faceBoundary g.1 ∧
          (interiorDualSpanningForest faceBoundary allFaces).dist
              f (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots f) <
            (interiorDualSpanningForest faceBoundary allFaces).dist
              g (interiorDualSpanningForestRoot faceBoundary allFaces roots hcoverRoots hsepRoots g))
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    InteriorDualBoundaryRootAdjDistancePeelData allFaces faceBoundary :=
  interiorDualBoundaryRootAdjDistancePeelDataOfCoverSeparatedBoundaryRootsCanonicalRootedSharedEdgeFaceMembershipCover
    (allFaces := allFaces) (peelFaces := peelFaces) (roots := roots)
    (faceBoundary := faceBoundary) hunique fallbackEdge hcoverRoots hsepRoots
    hpeelInterior
    (by
      intro r hr
      rcases hrootsBoundary r hr with ⟨e, her, heB⟩
      exact ⟨e, her, hboundarySupport heB⟩)
    hcover hchildren hall

/-- The weaker boundary-root adjacency-distance data canonically upgrades to the strongest
generic rooted-distance package on the ambient face subtype. This is the reusable theorem-layer
form of the current annulus-facing endpoint: after transporting to `ambientFaceBoundary`, the
remaining data is exactly a cover/separated-root adjacency-distance peel witness package. -/
noncomputable def InteriorDualBoundaryRootAdjDistancePeelData.toCoverSeparatedRootsAdjDistancePeelData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootAdjDistancePeelData allFaces faceBoundary) :
    CoverSeparatedRootsAdjDistancePeelData
      (interiorDualSpanningForest faceBoundary allFaces)
      allFaces.attach
      (ambientFaceBoundary (allFaces := allFaces) faceBoundary) := by
  let T := interiorDualSpanningForest faceBoundary allFaces
  let subBoundary : AmbientFace allFaces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := allFaces) faceBoundary
  let rootFace : AmbientFace allFaces → AmbientFace allFaces :=
    interiorDualSpanningForestRoot faceBoundary allFaces data.roots
      data.hcoverRoots data.hsepRoots
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
      rootFace data.fallbackEdge
  refine coverSeparatedRootsAdjDistancePeelDataOfWitnessCover
    T allFaces.attach data.peelFaces data.roots subBoundary witnessEdge
    (interiorDualSpanningForest_isAcyclic faceBoundary allFaces)
    ((rootSetCovers_congr_reachable data.roots
      (interiorDualSpanningForest_reachable_eq faceBoundary allFaces)).2 data.hcoverRoots)
    ((rootSetSeparated_congr_reachable data.roots
      (interiorDualSpanningForest_reachable_eq faceBoundary allFaces)).2 data.hsepRoots)
    ?_ ?_ ?_
  · intro e he
    have he' : e ∈ interiorEdgeSupport faceBoundary allFaces := by
      simpa [subBoundary, interiorEdgeSupport_ambientFaceBoundary_eq
        (faceBoundary := faceBoundary) (allFaces := allFaces)] using he
    simpa [witnessEdge] using data.hcover he'
  · intro f hf
    have hneq : f ≠ rootFace f :=
      ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
        faceBoundary allFaces data.peelFaces data.roots
        data.hcoverRoots data.hsepRoots
        (disjoint_peelFaces_roots_of_boundarySeparation
          faceBoundary allFaces data.peelFaces data.roots
          data.hpeelInterior data.hrootsBoundary)
        hf
    rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := f)
        (h := reachable_interiorDualSpanningForestRoot
          faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots f)
        hneq with ⟨p, hfp, _hadj, _hdist⟩
    simpa [subBoundary, witnessEdge, rootFace, ambientFaceBoundary] using
      rootedSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces data.hunique rootFace data.fallbackEdge hfp
  · intro f hf e he
    have he' : e ∈ (faceBoundary f.1).erase (witnessEdge f) := by
      simpa [subBoundary, witnessEdge, ambientFaceBoundary] using he
    have hef : e ∈ faceBoundary f.1 := (Finset.mem_erase.1 he').2
    rcases data.hchildren f hf e he' with hboundary | ⟨g, hg, hadj, heg, hlt⟩
    · exact Or.inl <| by
        simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using hboundary
    · have hroot : rootFace f = rootFace g := by
        simpa [rootFace] using
          interiorDualSpanningForestRoot_eq_of_adj
            faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots hadj
      have hgf : parentTowardsRoot T rootFace g = some f := by
        exact parentTowardsRoot_eq_some_of_adj_of_lt_dist_of_componentConstantRoot
          T (interiorDualSpanningForest_isAcyclic faceBoundary allFaces) rootFace hadj
          (reachable_interiorDualSpanningForestRoot
            faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots f)
          (reachable_interiorDualSpanningForestRoot
            faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots g)
          hroot hlt
      exact Or.inr ⟨g, hg, hadj,
        rootedSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
          faceBoundary allFaces data.hunique rootFace data.fallbackEdge
          data.hall hgf heg hef,
        hlt⟩

/-- The weaker boundary-root adjacency-distance data canonically upgrades to the generic finite
collar-layer witness-cover interface on the ambient face subtype. -/
noncomputable def InteriorDualBoundaryRootAdjDistancePeelData.toCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootAdjDistancePeelData allFaces faceBoundary) :
    CollarLayerFacePeelWitnessData allFaces.attach
      (ambientFaceBoundary (allFaces := allFaces) faceBoundary) :=
  data.toCoverSeparatedRootsAdjDistancePeelData.toCollarLayerFacePeelWitnessData

/-- The weaker boundary-root adjacency-distance data canonically upgrades to the strongest
boundary-root package by recovering the canonical `parentTowardsRoot` child relation from adjacency
and strict root-distance growth in the chosen interior-dual spanning forest. -/
noncomputable def InteriorDualBoundaryRootAdjDistancePeelData.toInteriorDualBoundaryRootParentPeelData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootAdjDistancePeelData allFaces faceBoundary) :
    InteriorDualBoundaryRootParentPeelData allFaces faceBoundary := by
  let T := interiorDualSpanningForest faceBoundary allFaces
  let rootFace : AmbientFace allFaces → AmbientFace allFaces :=
    interiorDualSpanningForestRoot faceBoundary allFaces data.roots
      data.hcoverRoots data.hsepRoots
  refine
    interiorDualBoundaryRootParentPeelDataOfCoverSeparatedBoundaryRootsCanonicalParentSharedEdgeFaceMembershipCover
      (allFaces := allFaces) (peelFaces := data.peelFaces) (roots := data.roots)
      (faceBoundary := faceBoundary) data.hunique data.fallbackEdge
      data.hcoverRoots data.hsepRoots data.hpeelInterior data.hrootsBoundary
      data.hcover ?_ data.hall
  intro f hf e he
  rcases data.hchildren f hf e he with hboundary | ⟨g, hg, hadj, heg, hlt⟩
  · exact Or.inl hboundary
  · refine Or.inr ⟨g, hg, ?_, heg⟩
    exact parentTowardsRoot_eq_some_of_adj_of_lt_dist_of_componentConstantRoot
      T (interiorDualSpanningForest_isAcyclic faceBoundary allFaces) rootFace hadj
      (reachable_interiorDualSpanningForestRoot
        faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots f)
      (reachable_interiorDualSpanningForestRoot
        faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots g)
      (by
        simpa [rootFace] using
          interiorDualSpanningForestRoot_eq_of_adj
            faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots hadj)
      hlt

theorem InteriorDualBoundaryRootAdjDistancePeelData.mem_roots_of_not_mem_peelFaces
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootAdjDistancePeelData allFaces faceBoundary)
    {f : AmbientFace allFaces} (hfPeel : f ∉ data.peelFaces) :
    f ∈ data.roots := by
  simpa using
    (data.toInteriorDualBoundaryRootParentPeelData.mem_roots_of_not_mem_peelFaces hfPeel)

theorem InteriorDualBoundaryRootAdjDistancePeelData.exists_mem_selectedBoundarySupport_of_not_mem_peelFaces
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootAdjDistancePeelData allFaces faceBoundary)
    {f : AmbientFace allFaces} (hfPeel : f ∉ data.peelFaces) :
    ∃ e ∈ faceBoundary f.1, e ∈ selectedBoundarySupport faceBoundary allFaces allFaces := by
  simpa using
    InteriorDualBoundaryRootParentPeelData.exists_mem_selectedBoundarySupport_of_not_mem_peelFaces
      data.toInteriorDualBoundaryRootParentPeelData hfPeel

/-- Certificate form of the weaker boundary-root adjacency-distance package. This first recovers
the canonical `parentTowardsRoot` relation inside the interior-dual spanning forest, then uses the
direct boundary-rooted parent certificate constructor. -/
noncomputable def InteriorDualBoundaryRootAdjDistancePeelData.toBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootAdjDistancePeelData allFaces faceBoundary) :
    BoundaryRootedFacePeelCertificate allFaces.attach
      (ambientFaceBoundary (allFaces := allFaces) faceBoundary) :=
  data.toInteriorDualBoundaryRootParentPeelData.toBoundaryRootedFacePeelCertificate

/-- Annihilator form of the weaker boundary-root adjacency-distance package. -/
theorem zero_on_ambientFaceSupport_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (data : InteriorDualBoundaryRootAdjDistancePeelData allFaces faceBoundary)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
          (interiorDualSpanningForestRoot faceBoundary allFaces data.roots
            data.hcoverRoots data.hsepRoots)
          data.fallbackEdge f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f))
              (C (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                (interiorDualSpanningForestRoot faceBoundary allFaces data.roots
                  data.hcoverRoots data.hsepRoots)
                data.fallbackEdge f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  let subBoundary : AmbientFace allFaces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := allFaces) faceBoundary
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
      (interiorDualSpanningForestRoot faceBoundary allFaces data.roots
        data.hcoverRoots data.hsepRoots)
      data.fallbackEdge
  have hall' : ∀ e, totalIncidenceCount subBoundary allFaces.attach e ≤ 2 := by
    intro e
    simpa [subBoundary, totalIncidenceCount_ambientFaceBoundary_eq
      (faceBoundary := faceBoundary) (allFaces := allFaces)] using data.hall e
  have hzeroBoundary' :
      ∀ e ∈ selectedBoundarySupport subBoundary allFaces.attach allFaces.attach, z e = 0 := by
    intro e he
    exact hzeroBoundary e <| by
      simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq
        (faceBoundary := faceBoundary) (allFaces := allFaces)] using he
  have horth' :
      ∀ f ∈ data.peelFaces,
        ∀ γ, γ ≠ 0 → γ ≠ C (witnessEdge f) →
          chainDot
              (boundaryBicoloredEdges C (C (witnessEdge f)) (C (witnessEdge f) + γ)
                (subBoundary f))
              z
              (polarizedFaceGenerator C (C (witnessEdge f)) (C (witnessEdge f) + γ)
                (subBoundary f)) = 0 := by
    intro f hf γ hγ0 hγd
    simpa [subBoundary, witnessEdge, ambientFaceBoundary] using horth f hf γ hγ0 hγd
  simpa [subBoundary, biUnion_attach_ambientFaceBoundary_eq
    (faceBoundary := faceBoundary) (allFaces := allFaces)] using
    zero_on_ambientFaceSupport_of_coverSeparatedRootsAdjDistancePeelData
      (C := C) (htait := htait) (z := z)
      (T := interiorDualSpanningForest faceBoundary allFaces)
      (allFaces := allFaces.attach) (faceBoundary := subBoundary)
      data.toCoverSeparatedRootsAdjDistancePeelData
      hall' hzeroBoundary' horth'

/-- Root-free height-and-parent data for the current interior-dual peeling route. This is the
layer-based target suggested by the annulus picture: peeled faces carry a parent in the chosen
interior-dual spanning forest and a height that strictly increases along parent edges. -/
structure InteriorDualHeightParentPeelData {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) where
  peelFaces : Finset (AmbientFace allFaces)
  hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces
  parentFace : AmbientFace allFaces → Option (AmbientFace allFaces)
  fallbackEdge : AmbientFace allFaces → G.edgeSet
  height : AmbientFace allFaces → ℕ
  hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p
  hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
    (interiorDualSpanningForest faceBoundary allFaces).Adj f p
  hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
    (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
      parentFace fallbackEdge hparentAdj)
  hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj f),
    e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
      ∃ g ∈ peelFaces, parentFace g = some f ∧ e ∈ faceBoundary g.1
  hheight : ∀ g ∈ peelFaces, ∀ f, parentFace g = some f → height f < height g
  hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2

/-- Named constructor for the height-ordered interior-dual peeling data. -/
def interiorDualHeightParentPeelDataOfHeightOrderedParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (height : AmbientFace allFaces → ℕ)
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ e ∈ faceBoundary g.1)
    (hheight : ∀ g ∈ peelFaces, ∀ f, parentFace g = some f → height f < height g)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    InteriorDualHeightParentPeelData allFaces faceBoundary :=
  { peelFaces := peelFaces
    hunique := hunique
    parentFace := parentFace
    fallbackEdge := fallbackEdge
    height := height
    hparent := hparent
    hparentAdj := hparentAdj
    hcover := hcover
    hchildren := hchildren
    hheight := hheight
    hall := hall }

/-- The height-ordered interior-dual peeling data canonically yields a boundary-rooted peel
certificate on the ambient face subtype. -/
noncomputable def InteriorDualHeightParentPeelData.toCollarLayerFacePeelWitnessData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualHeightParentPeelData allFaces faceBoundary) :
    CollarLayerFacePeelWitnessData allFaces.attach
      (ambientFaceBoundary (allFaces := allFaces) faceBoundary) := by
  let subBoundary : AmbientFace allFaces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := allFaces) faceBoundary
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
      data.parentFace data.fallbackEdge data.hparentAdj
  refine collarLayerFacePeelWitnessData_of_heightOrderedFacePeelWitnessCover
    allFaces.attach data.peelFaces subBoundary witnessEdge data.height ?_ ?_ ?_
  · simpa [subBoundary, witnessEdge, interiorEdgeSupport_ambientFaceBoundary_eq] using data.hcover
  · intro f hf
    rcases data.hparent f hf with ⟨p, hfp⟩
    simpa [subBoundary, witnessEdge, ambientFaceBoundary] using
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces data.hunique data.parentFace data.fallbackEdge data.hparentAdj hfp
  · intro f hf e he
    have he' : e ∈ (faceBoundary f.1).erase (witnessEdge f) := by
      simpa [subBoundary, witnessEdge, ambientFaceBoundary] using he
    have hef : e ∈ faceBoundary f.1 := (Finset.mem_erase.1 he').2
    rcases data.hchildren f hf e he' with hboundary | ⟨g, hg, hgf, heg⟩
    · exact Or.inl <| by
        simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using hboundary
    · refine Or.inr ⟨g, hg, ?_, data.hheight g hg f hgf⟩
      exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
        faceBoundary allFaces data.hunique data.parentFace data.fallbackEdge data.hparentAdj
        data.hall hgf heg hef

/-- The height-ordered interior-dual peeling data canonically yields a boundary-rooted peel
certificate on the ambient face subtype. -/
noncomputable def InteriorDualHeightParentPeelData.toBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualHeightParentPeelData allFaces faceBoundary) :
    BoundaryRootedFacePeelCertificate allFaces.attach
      (ambientFaceBoundary (allFaces := allFaces) faceBoundary) := by
  let subBoundary : AmbientFace allFaces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := allFaces) faceBoundary
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
      data.parentFace data.fallbackEdge data.hparentAdj
  refine boundaryRootedFacePeelCertificate_of_sortedHeightOrdered_parentFacePeelWitnessCover
    (allFaces := allFaces.attach) (peelFaces := data.peelFaces)
    (faceBoundary := subBoundary) (parentFace := data.parentFace)
    (witnessEdge := witnessEdge) (height := data.height) ?_ ?_ ?_ ?_
  · simpa [subBoundary, witnessEdge, interiorEdgeSupport_ambientFaceBoundary_eq] using data.hcover
  · intro f hf
    rcases data.hparent f hf with ⟨p, hfp⟩
    simpa [subBoundary, witnessEdge, ambientFaceBoundary] using
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces data.hunique data.parentFace data.fallbackEdge data.hparentAdj hfp
  · intro f hf e he
    have he' : e ∈ (faceBoundary f.1).erase (witnessEdge f) := by
      simpa [subBoundary, witnessEdge, ambientFaceBoundary] using he
    have hef : e ∈ faceBoundary f.1 := (Finset.mem_erase.1 he').2
    rcases data.hchildren f hf e he' with hboundary | ⟨g, hg, hgf, heg⟩
    · exact Or.inl <| by
        simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using hboundary
    · refine Or.inr ⟨g, hg, hgf, ?_⟩
      exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
        faceBoundary allFaces data.hunique data.parentFace data.fallbackEdge data.hparentAdj
        data.hall hgf heg hef
  · intro g hg f hgf
    exact data.hheight g hg f hgf

/-- Annihilator form of the packaged height-ordered interior-dual peeling data. -/
theorem zero_on_ambientFaceSupport_of_interiorDualHeightParentPeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (data : InteriorDualHeightParentPeelData allFaces faceBoundary)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
          data.parentFace data.fallbackEdge data.hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_interiorDualSpanningForest_heightOrdered_parentSharedEdgeFaceMembershipCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces)
    (peelFaces := data.peelFaces) (faceBoundary := faceBoundary)
    (hunique := data.hunique) (parentFace := data.parentFace)
    (fallbackEdge := data.fallbackEdge) (height := data.height)
    (hparent := data.hparent) (hparentAdj := data.hparentAdj)
    (hcover := data.hcover) (hchildren := data.hchildren) (hheight := data.hheight)
    (hall := data.hall) (hzeroBoundary := hzeroBoundary) (horth := horth)

/-- Height-ordered interior-dual peeling data canonically induces the weaker well-founded-parent
package by trimming the parent map outside the peeled faces. -/
noncomputable def InteriorDualHeightParentPeelData.toInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualHeightParentPeelData allFaces faceBoundary) :
    InteriorDualWellFoundedParentPeelData allFaces faceBoundary := by
  let peelParentFace : AmbientFace allFaces → Option (AmbientFace allFaces) :=
    fun f => if hf : f ∈ data.peelFaces then data.parentFace f else none
  have hparentAdj :
      ∀ {f p : AmbientFace allFaces}, peelParentFace f = some p →
        (interiorDualSpanningForest faceBoundary allFaces).Adj f p := by
    intro f p hfp
    by_cases hf : f ∈ data.peelFaces
    · have hfp' : data.parentFace f = some p := by
        simpa [peelParentFace, hf] using hfp
      exact data.hparentAdj hfp'
    · simp [peelParentFace, hf] at hfp
  let oldWitness : AmbientFace allFaces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
      data.parentFace data.fallbackEdge data.hparentAdj
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
      peelParentFace data.fallbackEdge hparentAdj
  have hwitnessEq : ∀ f ∈ data.peelFaces, witnessEdge f = oldWitness f := by
    intro f hf
    simp [witnessEdge, oldWitness, parentSharedInteriorEdgeOfPairwiseUnique, peelParentFace, hf]
  have hWF : WellFounded (ParentRel peelParentFace) := by
    refine wellFounded_parentRel_of_lt_height peelParentFace data.height ?_
    intro g f hgf
    by_cases hg : g ∈ data.peelFaces
    · have hgf' : data.parentFace g = some f := by
        simpa [peelParentFace, hg] using hgf
      exact data.hheight g hg f hgf'
    · simp [peelParentFace, hg] at hgf
  refine
    interiorDualWellFoundedParentPeelDataOfWellFoundedParentSharedEdgeFaceMembershipCover
      (allFaces := allFaces) (peelFaces := data.peelFaces) (faceBoundary := faceBoundary)
      data.hunique peelParentFace data.fallbackEdge hWF ?_ hparentAdj ?_ ?_ data.hall
  · intro f hf
    rcases data.hparent f hf with ⟨p, hfp⟩
    exact ⟨p, by simpa [peelParentFace, hf] using hfp⟩
  · intro e he
    rcases Finset.mem_image.1 (data.hcover he) with ⟨f, hf, hfe⟩
    exact Finset.mem_image.2 ⟨f, hf, (hwitnessEq f hf).trans hfe⟩
  · intro f hf e he
    have he' : e ∈ (faceBoundary f.1).erase (oldWitness f) := by
      simpa [witnessEdge, oldWitness, hwitnessEq f hf] using he
    rcases data.hchildren f hf e he' with hboundary | ⟨g, hg, hgf, heg⟩
    · exact Or.inl hboundary
    · refine Or.inr ⟨g, hg, ?_, heg⟩
      simpa [peelParentFace, hg] using hgf

/-- Root-distance parent data for the interior-dual peeling route. This packages the branch where
geometry supplies a parent relation in the chosen interior-dual spanning forest together with a
root assignment whose graph distance strictly decreases along parent edges. -/
structure InteriorDualRootDistanceParentPeelData {G : SimpleGraph V}
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet) where
  peelFaces : Finset (AmbientFace allFaces)
  hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces
  parentFace : AmbientFace allFaces → Option (AmbientFace allFaces)
  fallbackEdge : AmbientFace allFaces → G.edgeSet
  rootFace : AmbientFace allFaces → AmbientFace allFaces
  hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p
  hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
    (interiorDualSpanningForest faceBoundary allFaces).Adj f p
  hdist : ∀ {g f : AmbientFace allFaces}, parentFace g = some f →
    (interiorDualSpanningForest faceBoundary allFaces).dist f (rootFace f) <
      (interiorDualSpanningForest faceBoundary allFaces).dist g (rootFace g)
  hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
    (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
      parentFace fallbackEdge hparentAdj)
  hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj f),
    e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
      ∃ g ∈ peelFaces, parentFace g = some f ∧ e ∈ faceBoundary g.1
  hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2

/-- Named constructor for the root-distance parent branch of the interior-dual peeling route. -/
def interiorDualRootDistanceParentPeelDataOfParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (rootFace : AmbientFace allFaces → AmbientFace allFaces)
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hdist : ∀ {g f : AmbientFace allFaces}, parentFace g = some f →
      (interiorDualSpanningForest faceBoundary allFaces).dist f (rootFace f) <
        (interiorDualSpanningForest faceBoundary allFaces).dist g (rootFace g))
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ e ∈ faceBoundary g.1)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    InteriorDualRootDistanceParentPeelData allFaces faceBoundary :=
  { peelFaces := peelFaces
    hunique := hunique
    parentFace := parentFace
    fallbackEdge := fallbackEdge
    rootFace := rootFace
    hparent := hparent
    hparentAdj := hparentAdj
    hdist := hdist
    hcover := hcover
    hchildren := hchildren
    hall := hall }

/-- Root-distance interior-dual peeling data canonically induces height-ordered data by taking
height to be graph distance to the chosen root in the interior-dual spanning forest. -/
noncomputable def InteriorDualRootDistanceParentPeelData.toInteriorDualHeightParentPeelData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualRootDistanceParentPeelData allFaces faceBoundary) :
    InteriorDualHeightParentPeelData allFaces faceBoundary :=
  interiorDualHeightParentPeelDataOfHeightOrderedParentSharedEdgeFaceMembershipCover
    (allFaces := allFaces) (peelFaces := data.peelFaces) (faceBoundary := faceBoundary)
    data.hunique data.parentFace data.fallbackEdge
    (fun f => (interiorDualSpanningForest faceBoundary allFaces).dist f (data.rootFace f))
    data.hparent data.hparentAdj data.hcover data.hchildren
    (by
      intro g hg f hgf
      exact data.hdist hgf)
    data.hall

/-- Root-distance parent data canonically induces the weaker well-founded-parent package. -/
noncomputable def InteriorDualRootDistanceParentPeelData.toInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualRootDistanceParentPeelData allFaces faceBoundary) :
    InteriorDualWellFoundedParentPeelData allFaces faceBoundary :=
  data.toInteriorDualHeightParentPeelData.toInteriorDualWellFoundedParentPeelData

/-- The strongest boundary-root interior-dual data canonically induces explicit root-distance
parent data by taking shortest-path parents toward the separated covering root set. -/
noncomputable def InteriorDualBoundaryRootParentPeelData.toInteriorDualRootDistanceParentPeelData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootParentPeelData allFaces faceBoundary) :
    InteriorDualRootDistanceParentPeelData allFaces faceBoundary := by
  let T := interiorDualSpanningForest faceBoundary allFaces
  let rootFace : AmbientFace allFaces → AmbientFace allFaces :=
    interiorDualSpanningForestRoot faceBoundary allFaces data.roots
      data.hcoverRoots data.hsepRoots
  let parentFace : AmbientFace allFaces → Option (AmbientFace allFaces) :=
    parentTowardsRoot T rootFace
  have hdisj : Disjoint data.peelFaces data.roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      faceBoundary allFaces data.peelFaces data.roots
      data.hpeelInterior data.hrootsBoundary
  have hparent : ∀ f ∈ data.peelFaces, ∃ p, parentFace f = some p := by
    intro f hf
    have hneq : f ≠ rootFace f :=
      ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
        faceBoundary allFaces data.peelFaces data.roots
        data.hcoverRoots data.hsepRoots hdisj hf
    rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := f)
        (h := reachable_interiorDualSpanningForestRoot
          faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots f)
        hneq with ⟨p, hfp, _hadj, _hdist⟩
    exact ⟨p, hfp⟩
  have hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p → T.Adj f p := by
    intro f p hfp
    exact parentTowardsRoot_some_adj T rootFace hfp
  have hdist : ∀ {g f : AmbientFace allFaces}, parentFace g = some f →
      T.dist f (rootFace f) < T.dist g (rootFace g) := by
    intro g f hgf
    have hneq : g ≠ rootFace g := by
      intro hgr
      have hnone : parentFace g = none := by
        simpa [parentFace] using
          parentTowardsRoot_eq_none_of_eq_root (T := T) (root := rootFace) hgr
      rw [hgf] at hnone
      simp at hnone
    have hgf' : parentTowardsRoot T rootFace g = some f := by
      simpa [parentFace] using hgf
    rcases parentTowardsRoot_spec_of_ne (T := T) (root := rootFace) (u := g)
        (h := reachable_interiorDualSpanningForestRoot
          faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots g)
        hneq with ⟨w, hw, _hadj, hdist⟩
    rw [hgf'] at hw
    injection hw with hwf
    subst w
    have hroot : rootFace f = rootFace g := by
      exact interiorDualSpanningForestRoot_eq_of_adj
        faceBoundary allFaces data.roots data.hcoverRoots data.hsepRoots
        (parentTowardsRoot_some_adj T rootFace hgf').symm
    calc
      T.dist f (rootFace f) = T.dist f (rootFace g) := by rw [hroot]
      _ < T.dist f (rootFace g) + 1 := Nat.lt_succ_self _
      _ = T.dist g (rootFace g) := by rw [hdist]
  have hcover :
      interiorEdgeSupport faceBoundary allFaces ⊆ data.peelFaces.image
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
          parentFace data.fallbackEdge hparentAdj) := by
    intro e he
    rcases Finset.mem_image.mp (data.hcover he) with ⟨f, hf, hfe⟩
    exact Finset.mem_image.mpr ⟨f, hf, by
      simpa [parentFace, rootFace, rootedSharedInteriorEdgeOfPairwiseUnique] using hfe⟩
  have hchildren :
      ∀ f ∈ data.peelFaces, ∀ e ∈ (faceBoundary f.1).erase
          (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
            parentFace data.fallbackEdge hparentAdj f),
        e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
          ∃ g ∈ data.peelFaces, parentFace g = some f ∧ e ∈ faceBoundary g.1 := by
    intro f hf e he
    have he' : e ∈ (faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
          rootFace data.fallbackEdge f) := by
      simpa [parentFace, rootFace, rootedSharedInteriorEdgeOfPairwiseUnique] using he
    rcases data.hchildren f hf e he' with hboundary | ⟨g, hg, hgf, heg⟩
    · exact Or.inl hboundary
    · exact Or.inr ⟨g, hg, by simpa [parentFace] using hgf, heg⟩
  exact interiorDualRootDistanceParentPeelDataOfParentSharedEdgeFaceMembershipCover
    (allFaces := allFaces) (peelFaces := data.peelFaces) (faceBoundary := faceBoundary)
    data.hunique parentFace data.fallbackEdge rootFace
    hparent hparentAdj hdist hcover hchildren data.hall

/-- The strongest boundary-root interior-dual data also canonically induces the root-free
height-ordered package by composition through the root-distance layer. -/
noncomputable def InteriorDualBoundaryRootParentPeelData.toInteriorDualHeightParentPeelData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootParentPeelData allFaces faceBoundary) :
    InteriorDualHeightParentPeelData allFaces faceBoundary :=
  data.toInteriorDualRootDistanceParentPeelData.toInteriorDualHeightParentPeelData

/-- The strongest boundary-root interior-dual data also canonically induces the weaker
well-founded-parent package. -/
noncomputable def InteriorDualBoundaryRootParentPeelData.toInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootParentPeelData allFaces faceBoundary) :
    InteriorDualWellFoundedParentPeelData allFaces faceBoundary :=
  data.toInteriorDualRootDistanceParentPeelData.toInteriorDualWellFoundedParentPeelData

/-- The weaker boundary-root adjacency-distance data also canonically induces explicit
root-distance parent data by composition through the strongest boundary-root package. -/
noncomputable def InteriorDualBoundaryRootAdjDistancePeelData.toInteriorDualRootDistanceParentPeelData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootAdjDistancePeelData allFaces faceBoundary) :
    InteriorDualRootDistanceParentPeelData allFaces faceBoundary :=
  data.toInteriorDualBoundaryRootParentPeelData.toInteriorDualRootDistanceParentPeelData

/-- The weaker boundary-root adjacency-distance data also canonically induces the root-free
height-ordered package by composition through the root-distance layer. -/
noncomputable def InteriorDualBoundaryRootAdjDistancePeelData.toInteriorDualHeightParentPeelData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootAdjDistancePeelData allFaces faceBoundary) :
    InteriorDualHeightParentPeelData allFaces faceBoundary :=
  data.toInteriorDualRootDistanceParentPeelData.toInteriorDualHeightParentPeelData

/-- The weaker boundary-root adjacency-distance data also canonically induces the root-free
well-founded-parent package. -/
noncomputable def InteriorDualBoundaryRootAdjDistancePeelData.toInteriorDualWellFoundedParentPeelData
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualBoundaryRootAdjDistancePeelData allFaces faceBoundary) :
    InteriorDualWellFoundedParentPeelData allFaces faceBoundary :=
  data.toInteriorDualRootDistanceParentPeelData.toInteriorDualWellFoundedParentPeelData

/-- The root-distance parent data canonically yields a boundary-rooted peel certificate on the
ambient face subtype. -/
noncomputable def InteriorDualRootDistanceParentPeelData.toBoundaryRootedFacePeelCertificate
    {G : SimpleGraph V}
    {allFaces : Finset F} {faceBoundary : F → Finset G.edgeSet}
    (data : InteriorDualRootDistanceParentPeelData allFaces faceBoundary) :
    BoundaryRootedFacePeelCertificate allFaces.attach
      (ambientFaceBoundary (allFaces := allFaces) faceBoundary) := by
  let T := interiorDualSpanningForest faceBoundary allFaces
  let subBoundary : AmbientFace allFaces → Finset G.edgeSet :=
    ambientFaceBoundary (allFaces := allFaces) faceBoundary
  let witnessEdge : AmbientFace allFaces → G.edgeSet :=
    parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
      data.parentFace data.fallbackEdge data.hparentAdj
  have hWF : WellFounded (ParentRel data.parentFace) :=
    wellFounded_parentRel_of_rootDistance T data.parentFace data.rootFace
      (by
        intro g f hgf
        exact data.hdist hgf)
  have hcover' :
      interiorEdgeSupport subBoundary allFaces.attach ⊆ data.peelFaces.image witnessEdge := by
    simpa [subBoundary, witnessEdge, interiorEdgeSupport_ambientFaceBoundary_eq] using data.hcover
  have hwitness' : ∀ f ∈ data.peelFaces, witnessEdge f ∈ subBoundary f := by
    intro f hf
    rcases data.hparent f hf with ⟨p, hfp⟩
    simpa [subBoundary, witnessEdge, ambientFaceBoundary] using
      parentSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
        faceBoundary allFaces data.hunique data.parentFace data.fallbackEdge data.hparentAdj hfp
  have hchildren' :
      ∀ f ∈ data.peelFaces, ∀ e ∈ (subBoundary f).erase (witnessEdge f),
        e ∈ selectedBoundarySupport subBoundary allFaces.attach allFaces.attach ∨
          ∃ g ∈ data.peelFaces, data.parentFace g = some f ∧ witnessEdge g = e := by
    intro f hf e he
    have he' : e ∈ (faceBoundary f.1).erase (witnessEdge f) := by
      simpa [subBoundary, witnessEdge, ambientFaceBoundary] using he
    have hef : e ∈ faceBoundary f.1 := (Finset.mem_erase.1 he').2
    rcases data.hchildren f hf e he' with hboundary | ⟨g, hg, hgf, heg⟩
    · exact Or.inl <| by
        simpa [subBoundary, selectedBoundarySupport_ambientFaceBoundary_eq] using hboundary
    · refine Or.inr ⟨g, hg, hgf, ?_⟩
      exact parentSharedInteriorEdgeOfPairwiseUnique_eq_of_mem_faceBoundary
        faceBoundary allFaces data.hunique data.parentFace data.fallbackEdge data.hparentAdj
        data.hall hgf heg hef
  exact boundaryRootedFacePeelCertificate_of_wellFounded_parentFacePeelWitnessCover
    (allFaces := allFaces.attach) (peelFaces := data.peelFaces)
    (faceBoundary := subBoundary) (parentFace := data.parentFace)
    (witnessEdge := witnessEdge) hWF hcover' hwitness' hchildren'

/-- Certificate-packaged form of the interior-dual root-distance parent route. This gives the
annulus side a direct certificate endpoint when it can produce peeled faces, a parent relation in
the chosen interior-dual spanning forest, and a strictly decreasing root-distance assignment. -/
noncomputable def
    boundaryRootedFacePeelCertificate_of_interiorDualSpanningForest_rootDistanceParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V}
    (allFaces : Finset F)
    (peelFaces : Finset (AmbientFace allFaces))
    (faceBoundary : F → Finset G.edgeSet)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (parentFace : AmbientFace allFaces → Option (AmbientFace allFaces))
    (fallbackEdge : AmbientFace allFaces → G.edgeSet)
    (rootFace : AmbientFace allFaces → AmbientFace allFaces)
    (hparent : ∀ f ∈ peelFaces, ∃ p, parentFace f = some p)
    (hparentAdj : ∀ {f p : AmbientFace allFaces}, parentFace f = some p →
      (interiorDualSpanningForest faceBoundary allFaces).Adj f p)
    (hdist : ∀ {g f : AmbientFace allFaces}, parentFace g = some f →
      (interiorDualSpanningForest faceBoundary allFaces).dist f (rootFace f) <
        (interiorDualSpanningForest faceBoundary allFaces).dist g (rootFace g))
    (hcover : interiorEdgeSupport faceBoundary allFaces ⊆ peelFaces.image
      (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
        parentFace fallbackEdge hparentAdj))
    (hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (faceBoundary f.1).erase
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces hunique
          parentFace fallbackEdge hparentAdj f),
      e ∈ selectedBoundarySupport faceBoundary allFaces allFaces ∨
        ∃ g ∈ peelFaces, parentFace g = some f ∧ e ∈ faceBoundary g.1)
    (hall : ∀ e, totalIncidenceCount faceBoundary allFaces e ≤ 2) :
    BoundaryRootedFacePeelCertificate allFaces.attach
      (ambientFaceBoundary (allFaces := allFaces) faceBoundary) :=
  (interiorDualRootDistanceParentPeelDataOfParentSharedEdgeFaceMembershipCover
      (allFaces := allFaces) (peelFaces := peelFaces) (faceBoundary := faceBoundary)
      hunique parentFace fallbackEdge rootFace hparent hparentAdj hdist hcover hchildren hall
    ).toBoundaryRootedFacePeelCertificate

/-- Annihilator form of the packaged root-distance parent data. -/
theorem zero_on_ambientFaceSupport_of_interiorDualRootDistanceParentPeelData
    {G : SimpleGraph V}
    (C : G.EdgeColoring Color) (htait : IsTaitEdgeColoring G C) (z : G.edgeSet → Color)
    (allFaces : Finset F) (faceBoundary : F → Finset G.edgeSet)
    (data : InteriorDualRootDistanceParentPeelData allFaces faceBoundary)
    (hzeroBoundary : ∀ e ∈ selectedBoundarySupport faceBoundary allFaces allFaces, z e = 0)
    (horth : ∀ f ∈ data.peelFaces,
      ∀ γ, γ ≠ 0 → γ ≠ C
        (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
          data.parentFace data.fallbackEdge data.hparentAdj f) →
        chainDot
            (boundaryBicoloredEdges C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (faceBoundary f.1))
            z
            (polarizedFaceGenerator C
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f))
              (C (parentSharedInteriorEdgeOfPairwiseUnique faceBoundary allFaces data.hunique
                data.parentFace data.fallbackEdge data.hparentAdj f) + γ)
              (faceBoundary f.1)) = 0) :
    ∀ e ∈ allFaces.biUnion faceBoundary, z e = 0 := by
  exact zero_on_ambientFaceSupport_of_interiorDualSpanningForest_rootDistanceParentSharedEdgeFaceMembershipCover
    (C := C) (htait := htait) (z := z) (allFaces := allFaces)
    (peelFaces := data.peelFaces) (faceBoundary := faceBoundary)
    (hunique := data.hunique) (parentFace := data.parentFace)
    (fallbackEdge := data.fallbackEdge) (rootFace := data.rootFace)
    (hparent := data.hparent) (hparentAdj := data.hparentAdj)
    (hdist := data.hdist) (hcover := data.hcover) (hchildren := data.hchildren)
    (hall := data.hall) (hzeroBoundary := hzeroBoundary) (horth := horth)

end Mettapedia.GraphTheory.FourColor
