import Mettapedia.GraphTheory.FourColor.Theorem49InteriorVerticesEndpointObstruction
import Mettapedia.GraphTheory.FourColor.Theorem49PlanarBoundaryPeeling
import Mathlib.Tactic

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

namespace Theorem49ForcingInteriorEdgeObstruction

variable {V : Type*} [DecidableEq V]

/-- Route-facing witness that a specific interior edge is unusable for peeled-face coverage:
every face incident to the edge already contains selected-boundary support. -/
structure ForcingInteriorEdgeWitness {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  edge : G.edgeSet
  heInterior : edge ∈ interiorEdgeSupport emb.faceBoundary emb.faces
  hforcing : ∀ {f : AmbientFace emb.faces},
    edge ∈ emb.faceBoundary f.1 →
      ∃ b ∈ emb.faceBoundary f.1,
        b ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces

/-- Positive local condition negating forcing interior edges: each interior edge has at least one
incident face whose entire boundary is free of selected-boundary support. -/
def EveryInteriorEdgeHasBoundaryFreeIncidentFace {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) : Prop :=
  ∀ {e : G.edgeSet},
    e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
      ∃ f : AmbientFace emb.faces,
        e ∈ emb.faceBoundary f.1 ∧
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)

/-- Data-valued version of `EveryInteriorEdgeHasBoundaryFreeIncidentFace`: for each interior
edge, choose an incident face whose boundary avoids the selected-boundary support. This is the
selector shape needed by later construction code, without asserting any compatibility between
the selected faces for distinct interior edges. -/
structure BoundaryFreeIncidentFaceSelector {G : SimpleGraph V}
    (emb : PlaneEmbeddingWithBoundary G) where
  faceOf : (e : G.edgeSet) →
    e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
      AmbientFace emb.faces
  edge_mem_faceOf : ∀ {e : G.edgeSet}
    (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
      e ∈ emb.faceBoundary (faceOf e he).1
  faceOf_disjoint_selectedBoundarySupport : ∀ {e : G.edgeSet}
    (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
      Disjoint (emb.faceBoundary (faceOf e he).1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)

theorem everyInteriorEdgeHasBoundaryFreeIncidentFace_of_boundaryFreeIncidentFaceSelector
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (selector : BoundaryFreeIncidentFaceSelector emb) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace emb := by
  intro e heInterior
  exact
    ⟨selector.faceOf e heInterior,
      selector.edge_mem_faceOf (e := e) heInterior,
      selector.faceOf_disjoint_selectedBoundarySupport (e := e) heInterior⟩

noncomputable def boundaryFreeIncidentFaceSelector_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hfree : EveryInteriorEdgeHasBoundaryFreeIncidentFace emb) :
    BoundaryFreeIncidentFaceSelector emb := by
  classical
  refine
    { faceOf := fun e heInterior => Classical.choose (hfree (e := e) heInterior)
      edge_mem_faceOf := ?_
      faceOf_disjoint_selectedBoundarySupport := ?_ }
  · intro e heInterior
    exact (Classical.choose_spec (hfree (e := e) heInterior)).1
  · intro e heInterior
    exact (Classical.choose_spec (hfree (e := e) heInterior)).2

theorem nonempty_boundaryFreeIncidentFaceSelector_iff_everyInteriorEdgeHasBoundaryFreeIncidentFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) ↔
      EveryInteriorEdgeHasBoundaryFreeIncidentFace emb := by
  constructor
  · rintro ⟨selector⟩
    exact everyInteriorEdgeHasBoundaryFreeIncidentFace_of_boundaryFreeIncidentFaceSelector selector
  · intro hfree
    exact
      ⟨boundaryFreeIncidentFaceSelector_of_everyInteriorEdgeHasBoundaryFreeIncidentFace hfree⟩

theorem
    everyInteriorEdgeHasBoundaryFreeIncidentFace_of_not_nonempty_forcingInteriorEdgeWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hno : ¬ Nonempty (ForcingInteriorEdgeWitness emb)) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace emb := by
  classical
  intro e heInterior
  by_contra hmissing
  apply hno
  refine ⟨
    { edge := e
      heInterior := heInterior
      hforcing := ?_ }⟩
  intro f heFace
  by_contra hnoSelected
  have hdisjoint :
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) := by
    rw [Finset.disjoint_left]
    intro b hbFace hbSelected
    exact hnoSelected ⟨b, hbFace, hbSelected⟩
  exact hmissing ⟨f, heFace, hdisjoint⟩

theorem
    not_nonempty_forcingInteriorEdgeWitness_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hfree : EveryInteriorEdgeHasBoundaryFreeIncidentFace emb) :
    ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  rintro ⟨hw⟩
  rcases hfree hw.heInterior with ⟨f, heFace, hdisjoint⟩
  rcases hw.hforcing heFace with ⟨b, hbFace, hbSelected⟩
  exact (Finset.disjoint_left.mp hdisjoint) hbFace hbSelected

theorem not_nonempty_forcingInteriorEdgeWitness_iff_everyInteriorEdgeHasBoundaryFreeIncidentFace
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    ¬ Nonempty (ForcingInteriorEdgeWitness emb) ↔
      EveryInteriorEdgeHasBoundaryFreeIncidentFace emb := by
  constructor
  · exact everyInteriorEdgeHasBoundaryFreeIncidentFace_of_not_nonempty_forcingInteriorEdgeWitness
  · exact not_nonempty_forcingInteriorEdgeWitness_of_everyInteriorEdgeHasBoundaryFreeIncidentFace

/-- The data-valued boundary-free selector surface is exactly the absence of a forcing interior
edge.  This removes the intermediate predicate from later route tests: a proposed source shell
must either construct such a selector or allow a concrete forcing edge. -/
theorem nonempty_boundaryFreeIncidentFaceSelector_iff_not_nonempty_forcingInteriorEdgeWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) ↔
      ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  constructor
  · intro hselector
    exact
      not_nonempty_forcingInteriorEdgeWitness_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
        ((nonempty_boundaryFreeIncidentFaceSelector_iff_everyInteriorEdgeHasBoundaryFreeIncidentFace).1
          hselector)
  · intro hnoForcing
    exact
      (nonempty_boundaryFreeIncidentFaceSelector_iff_everyInteriorEdgeHasBoundaryFreeIncidentFace).2
        (everyInteriorEdgeHasBoundaryFreeIncidentFace_of_not_nonempty_forcingInteriorEdgeWitness
          hnoForcing)

/-- Contrapositive form of the selector/forcing duality: failing to choose a boundary-free
incident face for every interior edge is exactly the existence of a forcing interior edge. -/
theorem not_nonempty_boundaryFreeIncidentFaceSelector_iff_nonempty_forcingInteriorEdgeWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G} :
    ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) ↔
      Nonempty (ForcingInteriorEdgeWitness emb) := by
  classical
  constructor
  · intro hnoSelector
    by_contra hnoForcing
    exact hnoSelector
      ((nonempty_boundaryFreeIncidentFaceSelector_iff_not_nonempty_forcingInteriorEdgeWitness).2
        hnoForcing)
  · intro hforcing hselector
    exact
      ((nonempty_boundaryFreeIncidentFaceSelector_iff_not_nonempty_forcingInteriorEdgeWitness).1
        hselector) hforcing

/-- Any explicit same-embedding witness carrying a property `P` together with a forcing
interior-edge witness refutes a universal theorem saying that `P` always yields a boundary-free
incident-face selector on that same embedding. -/
theorem
    not_forall_nonempty_boundaryFreeIncidentFaceSelector_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V} (P : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      P emb ∧ Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        P emb → Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  intro h
  rcases hWitness with ⟨emb, hP, hforce⟩
  exact
    (not_nonempty_boundaryFreeIncidentFaceSelector_iff_nonempty_forcingInteriorEdgeWitness).2
      hforce (h (emb := emb) hP)

/-- Any explicit same-embedding witness carrying a property `P` together with a forcing
interior-edge witness refutes a universal theorem saying that `P` excludes forcing interior
edges on that same embedding. This isolates the missing geometric burden directly, before any
annulus-root or construction-side lowering. -/
theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V} (P : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      P emb ∧ Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        P emb → ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  intro h
  rcases hWitness with ⟨emb, hP, hw⟩
  exact (h (emb := emb) hP) hw

/-- In particular, there is no universal same-embedding theorem saying that an honest
closed-walk annulus source excludes forcing interior edges. -/
theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb => Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
      hWitness

/-- The stronger reachability-plus-cyclic shell likewise does not universally exclude forcing
interior edges on the same embedding. -/
theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb)) ∧
          Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) →
            ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  intro h
  refine
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb =>
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb))
      hWitness ?_
  intro emb hP
  exact h hP.1 hP.2

/-- The weaker reachability-plus-selected-boundary-arc shell also does not universally exclude
forcing interior edges on the same embedding. -/
theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb)) ∧
          Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) →
            ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  intro h
  refine
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb =>
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb))
      hWitness ?_
  intro emb hP
  exact h hP.1 hP.2

/-- The abstract forcing-edge witness already rules out the peeled interior-dual package. -/
theorem false_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary)
    (hw : ForcingInteriorEdgeWitness emb) :
    False := by
  exact
    Mettapedia.GraphTheory.FourColor.Theorem49InteriorVerticesEndpointObstruction.false_of_interiorDualBoundaryRootAdjDistancePeelData_of_forcing_interiorEdge
      data hw.heInterior hw.hforcing

theorem not_nonempty_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hw : ForcingInteriorEdgeWitness emb) :
    ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  rintro ⟨data⟩
  exact false_of_interiorDualBoundaryRootAdjDistancePeelData data hw

/-- The canonical-parent boundary-root package has the same positive local consequence as the
adjacency-distance package: every interior edge is represented on some peeled face whose whole
boundary avoids selected-boundary support. -/
theorem everyInteriorEdgeHasBoundaryFreeIncidentFace_of_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace emb := by
  intro e heInterior
  have hdisj : Disjoint data.peelFaces data.roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      emb.faceBoundary emb.faces data.peelFaces data.roots
      data.hpeelInterior data.hrootsBoundary
  have hcovered :
      e ∈ data.peelFaces.image
        (rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces
          data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary
            emb.faces data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge) :=
    data.hcover heInterior
  rcases Finset.mem_image.1 hcovered with ⟨f, hfPeel, hWitness⟩
  have hneq :
      f ≠ interiorDualSpanningForestRoot emb.faceBoundary
        emb.faces data.roots data.hcoverRoots data.hsepRoots f :=
    ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
      emb.faceBoundary emb.faces
      data.peelFaces data.roots data.hcoverRoots data.hsepRoots hdisj hfPeel
  rcases parentTowardsRoot_spec_of_ne
      (T := interiorDualSpanningForest emb.faceBoundary emb.faces)
      (root := interiorDualSpanningForestRoot emb.faceBoundary
        emb.faces data.roots data.hcoverRoots data.hsepRoots)
      (u := f)
      (h := reachable_interiorDualSpanningForestRoot
        emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots f)
      hneq with ⟨p, hfp, _hadj, _hdist⟩
  have hfWitness :
      rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces
          data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary
            emb.faces data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge f ∈ emb.faceBoundary f.1 :=
    rootedSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
      emb.faceBoundary emb.faces
      data.hunique
      (interiorDualSpanningForestRoot emb.faceBoundary
        emb.faces data.roots data.hcoverRoots data.hsepRoots)
      data.fallbackEdge hfp
  exact ⟨f, by simpa [hWitness] using hfWitness, data.hpeelInterior f hfPeel⟩

/-- The parent-oriented package therefore also excludes forcing interior edges. -/
theorem not_nonempty_forcingInteriorEdgeWitness_of_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :
    ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_nonempty_forcingInteriorEdgeWitness_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
      (everyInteriorEdgeHasBoundaryFreeIncidentFace_of_interiorDualBoundaryRootParentPeelData
        data)

/-- A forcing interior edge rules out the parent-oriented boundary-root package directly. -/
theorem false_of_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (hw : ForcingInteriorEdgeWitness emb) :
    False := by
  exact
    not_nonempty_forcingInteriorEdgeWitness_of_interiorDualBoundaryRootParentPeelData
      data ⟨hw⟩

theorem not_nonempty_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hw : ForcingInteriorEdgeWitness emb) :
    ¬ Nonempty (InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) := by
  rintro ⟨data⟩
  exact false_of_interiorDualBoundaryRootParentPeelData data hw

/-- The parent-package face selected for an interior edge is chosen from the actual rooted
shared-edge cover, not from the weaker existential no-forcing consequence. -/
noncomputable def parentPeelFaceOfInteriorEdge
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    (e : G.edgeSet)
    (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    AmbientFace emb.faces :=
  Classical.choose (Finset.mem_image.1 (data.hcover he))

theorem parentPeelFaceOfInteriorEdge_mem_peelFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    parentPeelFaceOfInteriorEdge data e he ∈ data.peelFaces := by
  exact (Classical.choose_spec (Finset.mem_image.1 (data.hcover he))).1

theorem rootedSharedInteriorEdge_parentPeelFaceOfInteriorEdge_eq
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    rootedSharedInteriorEdgeOfPairwiseUnique
        emb.faceBoundary emb.faces data.hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          data.roots data.hcoverRoots data.hsepRoots)
        data.fallbackEdge
        (parentPeelFaceOfInteriorEdge data e he) = e := by
  exact (Classical.choose_spec (Finset.mem_image.1 (data.hcover he))).2

theorem parentPeelFaceOfInteriorEdge_edge_mem_faceBoundary
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    e ∈ emb.faceBoundary (parentPeelFaceOfInteriorEdge data e he).1 := by
  have hfPeel :
      parentPeelFaceOfInteriorEdge data e he ∈ data.peelFaces :=
    parentPeelFaceOfInteriorEdge_mem_peelFaces data he
  have hWitness :
      rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge
          (parentPeelFaceOfInteriorEdge data e he) = e :=
    rootedSharedInteriorEdge_parentPeelFaceOfInteriorEdge_eq data he
  have hdisj : Disjoint data.peelFaces data.roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      emb.faceBoundary emb.faces data.peelFaces data.roots
      data.hpeelInterior data.hrootsBoundary
  have hneq :
      parentPeelFaceOfInteriorEdge data e he ≠
        interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          data.roots data.hcoverRoots data.hsepRoots
          (parentPeelFaceOfInteriorEdge data e he) :=
    ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
      emb.faceBoundary emb.faces
      data.peelFaces data.roots data.hcoverRoots data.hsepRoots hdisj hfPeel
  rcases parentTowardsRoot_spec_of_ne
      (T := interiorDualSpanningForest emb.faceBoundary emb.faces)
      (root := interiorDualSpanningForestRoot emb.faceBoundary emb.faces
        data.roots data.hcoverRoots data.hsepRoots)
      (u := parentPeelFaceOfInteriorEdge data e he)
      (h := reachable_interiorDualSpanningForestRoot
        emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots
        (parentPeelFaceOfInteriorEdge data e he))
      hneq with ⟨p, hfp, _hadj, _hdist⟩
  have hfWitness :
      rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces
          data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge
          (parentPeelFaceOfInteriorEdge data e he) ∈
        emb.faceBoundary (parentPeelFaceOfInteriorEdge data e he).1 :=
    rootedSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
      emb.faceBoundary emb.faces
      data.hunique
      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
        data.roots data.hcoverRoots data.hsepRoots)
      data.fallbackEdge hfp
  simpa [hWitness] using hfWitness

theorem parentPeelFaceOfInteriorEdge_disjoint_selectedBoundarySupport
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    Disjoint
      (emb.faceBoundary (parentPeelFaceOfInteriorEdge data e he).1)
      (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces) :=
  data.hpeelInterior
    (parentPeelFaceOfInteriorEdge data e he)
    (parentPeelFaceOfInteriorEdge_mem_peelFaces data he)

/-- Selector-valued form of the parent-package local consequence.  This exposes the exact
object consumed by the boundary-free selector construction layer, rather than only the
propositional no-forcing consequence. -/
noncomputable def boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :
    BoundaryFreeIncidentFaceSelector emb where
  faceOf := fun e he => parentPeelFaceOfInteriorEdge data e he
  edge_mem_faceOf := by
    intro e he
    exact parentPeelFaceOfInteriorEdge_edge_mem_faceBoundary data he
  faceOf_disjoint_selectedBoundarySupport := by
    intro e he
    exact parentPeelFaceOfInteriorEdge_disjoint_selectedBoundarySupport data he

theorem nonempty_boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  ⟨boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data⟩

theorem boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_faceOf_mem_peelFaces
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data).faceOf
      e he ∈ data.peelFaces := by
  exact parentPeelFaceOfInteriorEdge_mem_peelFaces data he

theorem rootedSharedInteriorEdge_boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_faceOf_eq
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary)
    {e : G.edgeSet} (he : e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    rootedSharedInteriorEdgeOfPairwiseUnique
        emb.faceBoundary emb.faces data.hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          data.roots data.hcoverRoots data.hsepRoots)
        data.fallbackEdge
        ((boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data).faceOf
          e he) = e := by
  exact rootedSharedInteriorEdge_parentPeelFaceOfInteriorEdge_eq data he

theorem boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_injective
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootParentPeelData emb.faces emb.faceBoundary) :
    ∀ {e₁ e₂ : G.edgeSet}
      (he₁ : e₁ ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
      (he₂ : e₂ ∈ interiorEdgeSupport emb.faceBoundary emb.faces),
        (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data).faceOf
          e₁ he₁ =
        (boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data).faceOf
          e₂ he₂ → e₁ = e₂ := by
  intro e₁ e₂ he₁ he₂ hface
  have h₁ :=
    rootedSharedInteriorEdge_boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_faceOf_eq
      data he₁
  have h₂ :=
    rootedSharedInteriorEdge_boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData_faceOf_eq
      data he₂
  rw [hface] at h₁
  exact h₁.symm.trans h₂

/-- Source-fixed canonical-parent hypotheses directly supply the boundary-free selector surface.
This is the selector-valued positive form of the same closed-walk source constructor used by the
parent-route Theorem 4.9 bridge. -/
noncomputable def boundaryFreeIncidentFaceSelectorOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
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
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1) :
    BoundaryFreeIncidentFaceSelector emb :=
  boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData
    (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren)

/-- Degenerate source-fixed selector extraction for closed-walk sources with no interior edge
support.  The selector is vacuous in this case, but the theorem exercises the same route data
surface as the nondegenerate parent branch. -/
noncomputable def boundaryFreeIncidentFaceSelectorOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    BoundaryFreeIncidentFaceSelector emb :=
  boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData
    (interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      source hcoverRoots hsepRoots hnoInterior)

/-- Nonempty selector witness for the degenerate source-fixed closed-walk branch with no
interior-edge support. -/
theorem nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  ⟨boundaryFreeIncidentFaceSelectorOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
    source hcoverRoots hsepRoots hnoInterior⟩

/-- The degenerate source-fixed `NoInteriorEdges` shell is already incompatible with the named
local endpoint witness: `HasUnblockedInteriorEndpoint` would force a live interior edge. -/
theorem not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (_hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (_hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    ¬ HasUnblockedInteriorEndpoint emb := by
  intro hEndpoint
  have hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty :=
    interiorEdgeSupport_nonempty_of_hasUnblockedInteriorEndpoint hEndpoint
  rw [hnoInterior] at hInterior
  simp at hInterior

/-- The same degenerate closed-walk shell rules out a nonempty purified selected-boundary
interior-edge endpoint carrier. -/
theorem not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  intro hCarrier
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      source hcoverRoots hsepRoots hnoInterior
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)

/-- The older raw endpoint-support shell is likewise incompatible with the degenerate
source-fixed `NoInteriorEdges` branch. -/
theorem not_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      source.boundaryFaceRoots)
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    ¬ (Disjoint (interiorEdgeEndpointSupport emb)
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
      (interiorEdgeEndpointSupport emb).Nonempty) := by
  rintro ⟨hEndpointDisjoint, hRawCarrier⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      source hcoverRoots hsepRoots hnoInterior
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)

/-- The actual theorem-4.9 boundary-order `NoInteriorEdges` shell inherits the same endpoint
obstruction on the same embedding. -/
theorem not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    ¬ HasUnblockedInteriorEndpoint emb := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      source hcoverRoots hsepRoots hnoInterior

/-- The theorem-4.9 boundary-order `NoInteriorEdges` shell likewise rules out a nonempty
purified selected-boundary carrier. -/
theorem not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  intro hCarrier
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges
      boundaryData dartCycles hboundaryArc hcoverRoots hsepRoots hnoInterior
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)

/-- The actual theorem-4.9 boundary-order raw endpoint-support shell is equally incompatible
with the degenerate `NoInteriorEdges` branch. -/
theorem not_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hnoInterior : interiorEdgeSupport emb.faceBoundary emb.faces = ∅) :
    ¬ (Disjoint (interiorEdgeEndpointSupport emb)
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
      (interiorEdgeEndpointSupport emb).Nonempty) := by
  rintro ⟨hEndpointDisjoint, hRawCarrier⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges
      boundaryData dartCycles hboundaryArc hcoverRoots hsepRoots hnoInterior
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)

/-- Graph-level impossibility form for the honest closed-walk `NoInteriorEdges` shell together
with the named local endpoint witness. -/
theorem not_exists_embedding_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        interiorEdgeSupport emb.faceBoundary emb.faces = ∅ ∧
        HasUnblockedInteriorEndpoint emb := by
  rintro ⟨emb, source, hcoverRoots, hsepRoots, hnoInterior, hEndpoint⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      source hcoverRoots hsepRoots hnoInterior hEndpoint

/-- Graph-level impossibility form for the honest closed-walk `NoInteriorEdges` shell together
with a nonempty purified selected-boundary carrier. -/
theorem not_exists_embedding_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        interiorEdgeSupport emb.faceBoundary emb.faces = ∅ ∧
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  rintro ⟨emb, source, hcoverRoots, hsepRoots, hnoInterior, hCarrier⟩
  exact
    not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      source hcoverRoots hsepRoots hnoInterior hCarrier

/-- Graph-level impossibility form for the honest closed-walk `NoInteriorEdges` shell together
with the older raw endpoint-support surface. -/
theorem not_exists_embedding_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        interiorEdgeSupport emb.faceBoundary emb.faces = ∅ ∧
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        (interiorEdgeEndpointSupport emb).Nonempty := by
  rintro ⟨emb, source, hcoverRoots, hsepRoots, hnoInterior, hEndpointDisjoint, hRawCarrier⟩
  exact
    not_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      source hcoverRoots hsepRoots hnoInterior
      ⟨hEndpointDisjoint, hRawCarrier⟩

/-- Graph-level impossibility form for the actual theorem-4.9 boundary-order `NoInteriorEdges`
shell together with the named local endpoint witness. -/
theorem not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ _hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        interiorEdgeSupport emb.faceBoundary emb.faces = ∅ ∧
        HasUnblockedInteriorEndpoint emb := by
  rintro ⟨emb, boundaryData, dartCycles, hboundaryArc, hcoverRoots, hsepRoots,
    hnoInterior, hEndpoint⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges
      boundaryData dartCycles hboundaryArc hcoverRoots hsepRoots hnoInterior hEndpoint

/-- Graph-level impossibility form for the actual theorem-4.9 boundary-order `NoInteriorEdges`
shell together with a nonempty purified selected-boundary carrier. -/
theorem not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ _hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        interiorEdgeSupport emb.faceBoundary emb.faces = ∅ ∧
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  rintro ⟨emb, boundaryData, dartCycles, hboundaryArc, hcoverRoots, hsepRoots,
    hnoInterior, hCarrier⟩
  exact
    not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges
      boundaryData dartCycles hboundaryArc hcoverRoots hsepRoots hnoInterior hCarrier

/-- Graph-level impossibility form for the actual theorem-4.9 boundary-order `NoInteriorEdges`
shell together with the older raw endpoint-support surface. -/
theorem not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ _hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ _hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        interiorEdgeSupport emb.faceBoundary emb.faces = ∅ ∧
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        (interiorEdgeEndpointSupport emb).Nonempty := by
  rintro ⟨emb, boundaryData, dartCycles, hboundaryArc, hcoverRoots, hsepRoots,
    hnoInterior, hEndpointDisjoint, hRawCarrier⟩
  exact
    not_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsNoInteriorEdges
      boundaryData dartCycles hboundaryArc hcoverRoots hsepRoots hnoInterior
      ⟨hEndpointDisjoint, hRawCarrier⟩

/-- Honest closed-walk sources cannot instantiate the nonempty raw source-fixed canonical-parent
cover constructor.  The constructor would induce a height-ordered terminal peeled face whose
non-witness boundary edges all lie on the selected-boundary support.  Since peeled faces are
disjoint from that support, the terminal face has boundary size at most one, contradicting the
three-edge lower bound supplied by the honest facial closed walk. -/
theorem false_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_interiorEdgeSupport_nonempty
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
    False := by
  let parentData :=
    interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
  let heightData :=
    planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData
      parentData.toInteriorDualHeightParentPeelData
  rcases
      heightData.exists_terminal_face_selectedBoundary_remainders_of_interiorEdgeSupport_nonempty
        hInterior with
    ⟨f, hfHeight, hterminal⟩
  have hfParent : f ∈ parentData.peelFaces := by
    simpa [heightData, planarBoundaryHeightOrderedFacePeelWitnessData_of_interiorDualHeightParentPeelData,
      InteriorDualBoundaryRootParentPeelData.toInteriorDualHeightParentPeelData,
      InteriorDualRootDistanceParentPeelData.toInteriorDualHeightParentPeelData,
      interiorDualHeightParentPeelDataOfHeightOrderedParentSharedEdgeFaceMembershipCover,
      InteriorDualBoundaryRootParentPeelData.toInteriorDualRootDistanceParentPeelData,
      interiorDualRootDistanceParentPeelDataOfParentSharedEdgeFaceMembershipCover]
      using hfHeight
  have hfPeel : f ∈ peelFaces := by
    simpa [parentData,
      interiorDualBoundaryRootParentPeelDataOfClosedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover,
      interiorDualBoundaryRootParentPeelDataOfCoverSeparatedBoundaryRootsCanonicalParentSharedEdgeCover,
      interiorDualBoundaryRootParentPeelDataOfCoverSeparatedBoundaryRootsCanonicalParentSharedEdgeFaceMembershipCover]
      using hfParent
  have herase_empty :
      (emb.faceBoundary f.1).erase (heightData.witnessEdge f) = ∅ := by
    ext e
    constructor
    · intro he
      have hef : e ∈ emb.faceBoundary f.1 := (Finset.mem_erase.1 he).2
      have hselected :
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces :=
        hterminal e he
      exact False.elim ((Finset.disjoint_left.mp (hpeelInterior f hfPeel)) hef hselected)
    · intro he
      simp at he
  have hsubset :
      emb.faceBoundary f.1 ⊆ ({heightData.witnessEdge f} : Finset G.edgeSet) := by
    intro e he
    by_cases hEq : e = heightData.witnessEdge f
    · simp [hEq]
    · have herase :
          e ∈ (emb.faceBoundary f.1).erase (heightData.witnessEdge f) :=
        Finset.mem_erase.2 ⟨hEq, he⟩
      rw [herase_empty] at herase
      simp at herase
  have hle : (emb.faceBoundary f.1).card ≤ 1 := by
    have hle' :
        (emb.faceBoundary f.1).card ≤
          ({heightData.witnessEdge f} : Finset G.edgeSet).card :=
      Finset.card_le_card hsubset
    simpa using hle'
  have hthree : 3 ≤ (emb.faceBoundary f.1).card :=
    (source.closedWalks.faceBoundaryClosedWalk f).three_le_faceBoundary_card
  exact (not_lt_of_ge hthree) (Nat.lt_of_le_of_lt hle (by decide : (1 : ℕ) < 3))

/-- Degeneracy form of the closed-walk raw-cover obstruction: under the current source-fixed
canonical-parent shared-edge-cover contract, honest facial closed walks force the interior-edge
support to be empty.  Thus the only possible closed-walk source-fixed raw-cover instances are
the already-constructed no-interior-edge branch. -/
theorem interiorEdgeSupport_eq_empty_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
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
    interiorEdgeSupport emb.faceBoundary emb.faces = ∅ := by
  by_contra hnonempty
  exact
    false_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_of_interiorEdgeSupport_nonempty
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      (Finset.nonempty_iff_ne_empty.2 hnonempty)

/-- The stronger source-fixed raw canonical-parent shared-edge-cover shell still reaches the
boundary-free selector surface, but only through the already-forced no-interior-edge branch. -/
theorem nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
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
    Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  exact
    nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges
      source hcoverRoots hsepRoots
      (interiorEdgeSupport_eq_empty_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover)

/-- Graph-level degeneracy lowering for the honest closed-walk raw canonical-parent shared-edge
cover shell: every such witness already lies in the `NoInteriorEdges` branch. -/
theorem exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsNoInteriorEdges_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
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
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
      ∃ _hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
      ∃ _hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        source.boundaryFaceRoots,
        interiorEdgeSupport emb.faceBoundary emb.faces = ∅ := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    ⟨emb, source, hcoverRoots, hsepRoots,
      interiorEdgeSupport_eq_empty_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover⟩

/-- Graph-level selector lowering for the honest closed-walk raw canonical-parent shared-edge
cover shell.  The selector exists, but only because the shell already collapses to the
degenerate no-interior-edge branch on the same embedding. -/
theorem exists_embedding_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_boundaryFreeIncidentFaceSelector_of_exists_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
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
    ∃ emb : PlaneEmbeddingWithBoundary G,
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
        Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  rcases hG with
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover⟩
  exact
    ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover,
      nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
        source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover⟩

/-- The actual theorem-4.9 boundary-order raw canonical-parent shared-edge-cover shell is
degenerate already before adding any endpoint witness: it forces `interiorEdgeSupport = ∅` on
the same embedding. -/
theorem interiorEdgeSupport_eq_empty_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge)) :
    interiorEdgeSupport emb.faceBoundary emb.faces = ∅ := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    interiorEdgeSupport_eq_empty_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover

/-- The actual theorem-4.9 boundary-order raw canonical-parent shared-edge-cover shell still
reaches the selector surface on the same embedding, but only because the shell already forces
the induced closed-walk source into the no-interior-edge branch. -/
theorem nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge)) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    nonempty_boundaryFreeIncidentFaceSelector_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover

/-- The live theorem-4.9 boundary-order raw canonical-parent shared-edge-cover shell is
incompatible with a forcing interior edge on the same embedding. The raw-cover hypotheses already
force a boundary-free selector, while a forcing edge rules out every such selector. -/
theorem
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (hw : ForcingInteriorEdgeWitness emb) :
    False := by
  have hSelector : Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
    nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover
  have hnot : ¬ Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
    (not_nonempty_boundaryFreeIncidentFaceSelector_iff_nonempty_forcingInteriorEdgeWitness).2
      ⟨hw⟩
  exact hnot hSelector

/-- Graph-level impossibility form of the same forcing-edge obstruction. If the live
successor-cycle shell on some embedding still carries a forcing interior edge, then the raw
canonical-parent shared-edge-cover package cannot exist on that shell. -/
theorem
    not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V} :
    ¬ (∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        Nonempty (ForcingInteriorEdgeWitness emb)) := by
  rintro ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
    hpeelInterior, hcover, ⟨hw⟩⟩
  exact
    false_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_forcingInteriorEdgeWitness
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hw

/-- Graph-level degeneracy lowering for the actual theorem-4.9 boundary-order raw canonical-parent
shared-edge-cover shell: every such witness already has empty interior-edge support. -/
theorem exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_interiorEdgeSupport_eq_empty_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces = ∅ := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover,
      interiorEdgeSupport_eq_empty_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover⟩

/-- Graph-level selector lowering for the actual theorem-4.9 boundary-order raw canonical-parent
shared-edge-cover shell.  The selector witness is available, but only through the same
degenerate no-interior-edge collapse forced by the raw-cover hypotheses. -/
theorem exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_boundaryFreeIncidentFaceSelector_of_exists_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V}
    (hG : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge)) :
    ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        Nonempty (BoundaryFreeIncidentFaceSelector emb) := by
  rcases hG with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover⟩
  exact
    ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots, hsepRoots,
      hpeelInterior, hcover,
      nonempty_boundaryFreeIncidentFaceSelector_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
        boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
        hpeelInterior hcover⟩

/-- Under the current source-fixed raw canonical-parent shared-edge-cover contract, an honest
closed-walk source cannot also have the named local unblocked endpoint witness: the raw-cover
hypotheses force `interiorEdgeSupport = ∅`, while `HasUnblockedInteriorEndpoint` produces a live
interior edge. -/
theorem not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
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
    ¬ HasUnblockedInteriorEndpoint emb := by
  intro hEndpoint
  have hInterior : (interiorEdgeSupport emb.faceBoundary emb.faces).Nonempty :=
    interiorEdgeSupport_nonempty_of_hasUnblockedInteriorEndpoint hEndpoint
  have hEmpty :
      interiorEdgeSupport emb.faceBoundary emb.faces = ∅ :=
    interiorEdgeSupport_eq_empty_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
  rw [hEmpty] at hInterior
  simp at hInterior

/-- The same raw canonical-parent shared-edge-cover hypotheses also rule out a nonempty purified
selected-boundary interior-edge endpoint carrier on the same embedding, because such a carrier is
equivalent to `HasUnblockedInteriorEndpoint`. -/
theorem not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
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
    ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  intro hCarrier
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)

/-- The older raw endpoint-support shell is also incompatible with the source-fixed raw
canonical-parent shared-edge-cover contract, because endpoint-support separation plus a nonempty
raw interior-edge endpoint carrier already implies `HasUnblockedInteriorEndpoint`. -/
theorem not_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
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
    ¬ (Disjoint (interiorEdgeEndpointSupport emb)
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
      (interiorEdgeEndpointSupport emb).Nonempty) := by
  rintro ⟨hEndpointDisjoint, hRawCarrier⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)

/-- The actual theorem-4.9 boundary-order source shell inherits the same impossibility: once the
selected-boundary arc data is lowered to the induced honest closed-walk source, the stronger raw
canonical-parent shared-edge-cover contract still rules out `HasUnblockedInteriorEndpoint` on the
same embedding. -/
theorem not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge)) :
    ¬ HasUnblockedInteriorEndpoint emb := by
  let source :=
    PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
      boundaryData dartCycles hboundaryArc
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover

/-- The theorem-4.9 boundary-order raw canonical-parent shared-edge-cover shell likewise rules
out a nonempty purified selected-boundary carrier, by the same endpoint equivalence. -/
theorem not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge)) :
    ¬ (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  intro hCarrier
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover
      ((hasUnblockedInteriorEndpoint_iff_selectedBoundaryInteriorEdgeEndpointVertices_nonempty
        emb).2 hCarrier)

/-- The actual boundary-order raw endpoint-support shell is equally inconsistent: on this source
surface, endpoint-support separation and a nonempty raw interior-edge endpoint carrier still
collapse to the forbidden local endpoint witness. -/
theorem not_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge)) :
    ¬ (Disjoint (interiorEdgeEndpointSupport emb)
        (edgeEndpointSupport
          (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
      (interiorEdgeEndpointSupport emb).Nonempty) := by
  rintro ⟨hEndpointDisjoint, hRawCarrier⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover
      (hasUnblockedInteriorEndpoint_of_endpointSupport_disjoint_and_nonempty
        hEndpointDisjoint hRawCarrier)

/-- The stricter source-fixed canonical-parent shared-edge face-membership shell is equally
incompatible with the named local unblocked endpoint witness, since it already contains the raw
canonical-parent shared-edge-cover hypotheses that force the no-interior-edge branch. -/
theorem not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
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
    (_hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            source.boundaryFaceRoots hcoverRoots hsepRoots)
          source.fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1) :
    ¬ HasUnblockedInteriorEndpoint emb := by
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover

/-- The theorem-4.9 boundary-order face-membership shell inherits the same endpoint impossibility:
after lowering to the induced honest closed-walk source, the stricter child-membership package
still cannot coexist with `HasUnblockedInteriorEndpoint` on the same embedding. -/
theorem
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb)
    (dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb)
    (hboundaryArc : ∀ f : AmbientFace emb.faces,
      (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
        |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f)
    (peelFaces : Finset (AmbientFace emb.faces))
    (hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces)
    (hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
        boundaryData dartCycles hboundaryArc).boundaryFaceRoots)
    (hpeelInterior : ∀ f ∈ peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hcover : interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
      (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
        (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).boundaryFaceRoots
          hcoverRoots hsepRoots)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).fallbackEdge))
    (_hchildren : ∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
        (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
            hcoverRoots hsepRoots)
          (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).fallbackEdge f),
      e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
        ∃ g ∈ peelFaces,
          parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots) g = some f ∧
          e ∈ emb.faceBoundary g.1) :
    ¬ HasUnblockedInteriorEndpoint emb := by
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover

/-- Graph-level impossibility form for the honest closed-walk raw canonical-parent cover plus the
named local endpoint witness.  The downstream parent, selector, and residual theorem-4.9 routes
from this source-fixed package are therefore vacuous under the current endpoint semantics. -/
theorem not_exists_embedding_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
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
        HasUnblockedInteriorEndpoint emb := by
  rintro ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots,
    hpeelInterior, hcover, hEndpoint⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hEndpoint

/-- Graph-level impossibility form for the honest closed-walk stricter canonical-parent
face-membership shell together with the named local endpoint witness.  The corresponding
selector-based and direct projected routes from that stronger shell are therefore vacuous under
the current endpoint semantics. -/
theorem not_exists_embedding_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
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
              e ∈ emb.faceBoundary g.1) ∧
        HasUnblockedInteriorEndpoint emb := by
  rintro ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots,
    hpeelInterior, hcover, hchildren, hEndpoint⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint

/-- Graph-level impossibility form for the honest closed-walk raw canonical-parent cover plus a
nonempty purified selected-boundary carrier. -/
theorem not_exists_embedding_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
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
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  rintro ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots,
    hpeelInterior, hcover, hCarrier⟩
  exact
    not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hCarrier

/-- Graph-level impossibility form for the actual theorem-4.9 boundary-order raw canonical-parent
cover shell together with the named local endpoint witness. -/
theorem not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        HasUnblockedInteriorEndpoint emb := by
  rintro ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique,
    hcoverRoots, hsepRoots, hpeelInterior, hcover, hEndpoint⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hEndpoint

/-- Graph-level impossibility form for the actual theorem-4.9 boundary-order stricter
canonical-parent face-membership shell together with the named local endpoint witness. -/
theorem not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
            (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
              (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                hcoverRoots hsepRoots)
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).fallbackEdge f),
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
            ∃ g ∈ peelFaces,
              parentTowardsRoot (interiorDualSpanningForest emb.faceBoundary emb.faces)
                  (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                    hcoverRoots hsepRoots) g = some f ∧
              e ∈ emb.faceBoundary g.1) ∧
        HasUnblockedInteriorEndpoint emb := by
  rintro ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique, hcoverRoots,
    hsepRoots, hpeelInterior, hcover, hchildren, hEndpoint⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hchildren hEndpoint

/-- Any explicit same-embedding witness of an honest closed-walk source together with the named
local endpoint witness already refutes a universal derivation of the stronger source-fixed
canonical-parent face-membership shell.  This isolates the real burden sharply: the shell is not
blocked only by exact-v23 or coloring data, but already by the endpoint semantics themselves. -/
theorem
    not_forall_some_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_closedWalkAnnulusBoundarySource_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        HasUnblockedInteriorEndpoint emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          HasUnblockedInteriorEndpoint emb →
            ∃ source : PlanarBoundaryClosedWalkAnnulusBoundarySource emb,
              ∃ peelFaces : Finset (AmbientFace emb.faces),
              ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
              ∃ hcoverRoots : RootSetCovers
                (interiorDualGraph emb.faceBoundary emb.faces)
                source.boundaryFaceRoots,
              ∃ hsepRoots : RootSetSeparated
                (interiorDualGraph emb.faceBoundary emb.faces)
                source.boundaryFaceRoots,
                (∀ f ∈ peelFaces,
                  Disjoint (emb.faceBoundary f.1)
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
                interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
                  (rootedSharedInteriorEdgeOfPairwiseUnique
                    emb.faceBoundary emb.faces hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                      source.boundaryFaceRoots hcoverRoots hsepRoots)
                    source.fallbackEdge) ∧
                (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                    (rootedSharedInteriorEdgeOfPairwiseUnique
                      emb.faceBoundary emb.faces hunique
                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                        source.boundaryFaceRoots hcoverRoots hsepRoots)
                      source.fallbackEdge f),
                  e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                    ∃ g ∈ peelFaces,
                      parentTowardsRoot
                          (interiorDualSpanningForest emb.faceBoundary emb.faces)
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            source.boundaryFaceRoots hcoverRoots hsepRoots) g = some f ∧
                      e ∈ emb.faceBoundary g.1) := by
  intro h
  rcases hWitness with ⟨emb, hSource, hEndpoint⟩
  rcases h emb hSource hEndpoint with
    ⟨source, peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover hchildren hEndpoint

/-- The same converse failure holds directly on the live successor-cycle shell: any same-embedding
endpoint witness already refutes a universal theorem deriving the stronger canonical-parent
face-membership shell from boundary reachability plus successor-cycle data alone. -/
theorem
    not_forall_some_successorCycleBoundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover_of_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_hasUnblockedInteriorEndpoint
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
          (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
            |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
            boundaryData dartCycles hboundaryArc).toPlanarBoundaryAnnulusBoundaryData =
          boundaryData.toPlanarBoundaryAnnulusBoundaryData ∧
        HasUnblockedInteriorEndpoint emb) :
    ¬ ∀ emb : PlaneEmbeddingWithBoundary G,
        ∀ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∀ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
        ∀ hboundaryArc : ∀ f : AmbientFace emb.faces,
            (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
              |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
          HasUnblockedInteriorEndpoint emb →
            ∃ peelFaces : Finset (AmbientFace emb.faces),
              ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
              ∃ hcoverRoots : RootSetCovers
                (interiorDualGraph emb.faceBoundary emb.faces)
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
              ∃ hsepRoots : RootSetSeparated
                (interiorDualGraph emb.faceBoundary emb.faces)
                (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                  boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
                (∀ f ∈ peelFaces,
                  Disjoint (emb.faceBoundary f.1)
                    (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
                interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
                  (rootedSharedInteriorEdgeOfPairwiseUnique
                    emb.faceBoundary emb.faces hunique
                    (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                      hcoverRoots hsepRoots)
                    (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                      boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
                (∀ f ∈ peelFaces, ∀ e ∈ (emb.faceBoundary f.1).erase
                    (rootedSharedInteriorEdgeOfPairwiseUnique
                      emb.faceBoundary emb.faces hunique
                      (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                          boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                        hcoverRoots hsepRoots)
                      (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                        boundaryData dartCycles hboundaryArc).fallbackEdge f),
                  e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∨
                    ∃ g ∈ peelFaces,
                      parentTowardsRoot
                          (interiorDualSpanningForest emb.faceBoundary emb.faces)
                          (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
                            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                              boundaryData dartCycles hboundaryArc).boundaryFaceRoots
                            hcoverRoots hsepRoots) g = some f ∧
                      e ∈ emb.faceBoundary g.1) := by
  intro h
  rcases hWitness with
    ⟨emb, boundaryData, dartCycles, hboundaryArc, _hboundaryEq, hEndpoint⟩
  rcases h emb boundaryData dartCycles hboundaryArc hEndpoint with
    ⟨peelFaces, hunique, hcoverRoots, hsepRoots, hpeelInterior, hcover, hchildren⟩
  exact
    not_hasUnblockedInteriorEndpoint_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeFaceMembershipCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hchildren hEndpoint

/-- Graph-level impossibility form for the actual theorem-4.9 boundary-order raw canonical-parent
cover shell plus a nonempty purified selected-boundary carrier. -/
theorem not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_nonempty_selectedBoundaryInteriorEdgeEndpointVertices
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        (selectedBoundaryInteriorEdgeEndpointVertices emb).Nonempty := by
  rintro ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique,
    hcoverRoots, hsepRoots, hpeelInterior, hcover, hCarrier⟩
  exact
    not_nonempty_selectedBoundaryInteriorEdgeEndpointVertices_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover hCarrier

/-- Graph-level impossibility form for the honest closed-walk raw canonical-parent cover plus
the older raw endpoint-support shell. -/
theorem not_exists_embedding_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
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
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        (interiorEdgeEndpointSupport emb).Nonempty := by
  rintro ⟨emb, source, peelFaces, hunique, hcoverRoots, hsepRoots,
    hpeelInterior, hcover, hEndpointDisjoint, hRawCarrier⟩
  exact
    not_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_of_closedWalkAnnulusBoundarySourceBoundaryFaceRootsCanonicalParentSharedEdgeCover
      source peelFaces hunique hcoverRoots hsepRoots hpeelInterior hcover
      ⟨hEndpointDisjoint, hRawCarrier⟩

/-- Graph-level impossibility form for the actual theorem-4.9 boundary-order raw canonical-parent
cover shell plus the older raw endpoint-support surface. -/
theorem not_exists_embedding_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover_and_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ boundaryData : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
      ∃ dartCycles : PlanarBoundaryDartSuccessorCycleEmbeddingData emb,
      ∃ hboundaryArc : ∀ f : AmbientFace emb.faces,
        (dartCycles.toPlanarBoundaryClosedWalkEmbeddingData
          |>.toPlanarBoundaryFaceBoundaryRunGeometry).SelectedBoundaryArcOnFace f,
      ∃ peelFaces : Finset (AmbientFace emb.faces),
      ∃ hunique : PairwiseUniqueSharedInteriorEdges emb.faceBoundary emb.faces,
      ∃ hcoverRoots : RootSetCovers (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
      ∃ hsepRoots : RootSetSeparated (interiorDualGraph emb.faceBoundary emb.faces)
        (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
          boundaryData dartCycles hboundaryArc).boundaryFaceRoots,
        (∀ f ∈ peelFaces,
          Disjoint (emb.faceBoundary f.1)
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        interiorEdgeSupport emb.faceBoundary emb.faces ⊆ peelFaces.image
          (rootedSharedInteriorEdgeOfPairwiseUnique emb.faceBoundary emb.faces hunique
            (interiorDualSpanningForestRoot emb.faceBoundary emb.faces
              (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
                boundaryData dartCycles hboundaryArc).boundaryFaceRoots
              hcoverRoots hsepRoots)
            (PlanarBoundaryClosedWalkAnnulusBoundarySource.ofDartSuccessorCycleFields
              boundaryData dartCycles hboundaryArc).fallbackEdge) ∧
        Disjoint (interiorEdgeEndpointSupport emb)
          (edgeEndpointSupport
            (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces)) ∧
        (interiorEdgeEndpointSupport emb).Nonempty := by
  rintro ⟨emb, boundaryData, dartCycles, hboundaryArc, peelFaces, hunique,
    hcoverRoots, hsepRoots, hpeelInterior, hcover, hEndpointDisjoint, hRawCarrier⟩
  exact
    not_endpointSupport_disjoint_and_nonempty_interiorEdgeEndpointSupport_of_boundaryReachabilityData_and_dartSuccessorCycleEmbeddingData_and_selectedBoundaryArc_and_boundaryFaceRootsCanonicalParentSharedEdgeCover
      boundaryData dartCycles hboundaryArc peelFaces hunique hcoverRoots hsepRoots
      hpeelInterior hcover ⟨hEndpointDisjoint, hRawCarrier⟩

/-- The interior-dual boundary-root adjacency-distance package directly supplies the positive
local no-forcing condition: every interior edge is covered by a peeled witness face whose whole
boundary is disjoint from the selected-boundary support. -/
theorem everyInteriorEdgeHasBoundaryFreeIncidentFace_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace emb := by
  intro e heInterior
  have hdisj : Disjoint data.peelFaces data.roots :=
    disjoint_peelFaces_roots_of_boundarySeparation
      emb.faceBoundary emb.faces data.peelFaces data.roots
      data.hpeelInterior data.hrootsBoundary
  have hcovered :
      e ∈ data.peelFaces.image
        (rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces
          data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary
            emb.faces data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge) :=
    data.hcover heInterior
  rcases Finset.mem_image.1 hcovered with ⟨f, hfPeel, hWitness⟩
  have hneq :
      f ≠ interiorDualSpanningForestRoot emb.faceBoundary
        emb.faces data.roots data.hcoverRoots data.hsepRoots f :=
    ne_interiorDualSpanningForestRoot_of_mem_peelFaces_of_disjoint_roots
      emb.faceBoundary emb.faces
      data.peelFaces data.roots data.hcoverRoots data.hsepRoots hdisj hfPeel
  rcases parentTowardsRoot_spec_of_ne
      (T := interiorDualSpanningForest emb.faceBoundary emb.faces)
      (root := interiorDualSpanningForestRoot emb.faceBoundary
        emb.faces data.roots data.hcoverRoots data.hsepRoots)
      (u := f)
      (h := reachable_interiorDualSpanningForestRoot
        emb.faceBoundary emb.faces data.roots data.hcoverRoots data.hsepRoots f)
      hneq with ⟨p, hfp, _hadj, _hdist⟩
  have hfWitness :
      rootedSharedInteriorEdgeOfPairwiseUnique
          emb.faceBoundary emb.faces
          data.hunique
          (interiorDualSpanningForestRoot emb.faceBoundary
            emb.faces data.roots data.hcoverRoots data.hsepRoots)
          data.fallbackEdge f ∈ emb.faceBoundary f.1 :=
    rootedSharedInteriorEdgeOfPairwiseUnique_mem_faceBoundary
      emb.faceBoundary emb.faces
      data.hunique
      (interiorDualSpanningForestRoot emb.faceBoundary
        emb.faces data.roots data.hcoverRoots data.hsepRoots)
      data.fallbackEdge hfp
  exact ⟨f, by simpa [hWitness] using hfWitness, data.hpeelInterior f hfPeel⟩

/-- Package the same adjacency-distance no-forcing criterion as explicit selector data. -/
noncomputable def boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    BoundaryFreeIncidentFaceSelector emb :=
  boundaryFreeIncidentFaceSelector_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
    (everyInteriorEdgeHasBoundaryFreeIncidentFace_of_interiorDualBoundaryRootAdjDistancePeelData
      data)

theorem nonempty_boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  ⟨boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootAdjDistancePeelData data⟩

/-- Contrapositive-free form of the same criterion: once the interior-dual boundary-root
adjacency-distance package is present, no forcing interior-edge witness can exist. -/
theorem not_nonempty_forcingInteriorEdgeWitness_of_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :
    ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_nonempty_forcingInteriorEdgeWitness_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
      (everyInteriorEdgeHasBoundaryFreeIncidentFace_of_interiorDualBoundaryRootAdjDistancePeelData
        data)

/-- Since the two-sided annulus-root package contains interior-dual boundary-root adjacency-
distance data, the same forcing-edge witness already rules out the annulus-root route data
itself. -/
theorem false_of_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb)
    (hw : ForcingInteriorEdgeWitness emb) :
    False := by
  exact false_of_interiorDualBoundaryRootAdjDistancePeelData data.interiorData hw

theorem not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hw : ForcingInteriorEdgeWitness emb) :
    ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  rintro ⟨data⟩
  exact false_of_planarBoundaryAnnulusRootAdjDistancePeelData data hw

theorem everyInteriorEdgeHasBoundaryFreeIncidentFace_of_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace emb :=
  everyInteriorEdgeHasBoundaryFreeIncidentFace_of_interiorDualBoundaryRootAdjDistancePeelData
    data.interiorData

noncomputable def boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb) :
    BoundaryFreeIncidentFaceSelector emb :=
  boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootAdjDistancePeelData
    data.interiorData

theorem nonempty_boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootAdjDistancePeelData emb) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  ⟨boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusRootAdjDistancePeelData data⟩

/-- Since the two-sided annulus-root parent package contains the generic parent payload, a
forcing edge rules out that source-facing sufficiency target as well. -/
theorem false_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb)
    (hw : ForcingInteriorEdgeWitness emb) :
    False := by
  exact false_of_interiorDualBoundaryRootParentPeelData data.interiorData hw

theorem not_nonempty_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hw : ForcingInteriorEdgeWitness emb) :
    ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  rintro ⟨data⟩
  exact false_of_planarBoundaryAnnulusRootParentPeelData data hw

noncomputable def boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb) :
    BoundaryFreeIncidentFaceSelector emb :=
  boundaryFreeIncidentFaceSelector_of_interiorDualBoundaryRootParentPeelData data.interiorData

theorem nonempty_boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusRootParentPeelData emb) :
    Nonempty (BoundaryFreeIncidentFaceSelector emb) :=
  ⟨boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusRootParentPeelData data⟩

/-- Any explicit same-embedding witness carrying a property `P` together with a forcing
interior-edge witness refutes a universal derivation theorem from `P` to the current two-sided
annulus-root parent package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V} (P : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      P emb ∧ Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        P emb → Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  rcases hWitness with ⟨emb, hP, ⟨hw⟩⟩
  exact not_nonempty_planarBoundaryAnnulusRootParentPeelData (emb := emb) hw
    (h (emb := emb) hP)

/-- The same forcing-edge witness also blocks any universal converse from the final theorem-4.9
boundary-root synthesis endpoint back to the stronger same-embedding parent-peel package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (∃ C : G.EdgeColoring Color,
        IsTaitEdgeColoring G C ∧ Theorem49BoundaryRootSynthesis emb C) ∧
          Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (C : G.EdgeColoring Color),
        IsTaitEdgeColoring G C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb =>
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧ Theorem49BoundaryRootSynthesis emb C)
      hWitness ?_
  intro emb hP
  rcases hP with ⟨C, hC, hSynthesis⟩
  exact h C hC hSynthesis

/-- Route-facing special case of the generic failed converse: an honest closed-walk annulus
source can coexist with a forcing interior edge on some embedding, so there is no universal
same-embedding derivation from that source shell to annulus-root parent data. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb => Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
      hWitness

/-- The same forcing-edge witness blocks any universal same-embedding derivation from annulus
boundary reachability plus cyclic ordered face-arc data to annulus-root parent data. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb)) ∧
          Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) →
            Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb =>
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb))
      hWitness ?_
  intro emb hP
  exact h hP.1 hP.2

/-- The same forcing-edge witness also blocks the weaker same-embedding derivation from annulus
boundary reachability plus bundled selected-boundary arc geometry to annulus-root parent data. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb)) ∧
          Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) →
            Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusRootParentPeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb =>
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb))
      hWitness ?_
  intro emb hP
  exact h hP.1 hP.2

/-- Any explicit same-embedding witness carrying a property `P` together with a forcing
interior-edge witness refutes a universal derivation theorem from `P` to the current two-sided
annulus-root adjacency-distance package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V} (P : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      P emb ∧ Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        P emb → Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  intro h
  rcases hWitness with ⟨emb, hP, ⟨hw⟩⟩
  exact not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData (emb := emb) hw
    (h (emb := emb) hP)

/-- The same forcing-edge witness also blocks any universal converse from the final theorem-4.9
boundary-root synthesis endpoint back to the weaker same-embedding annulus-root
adjacency-distance package. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_taitEdgeColoring_and_theorem49BoundaryRootSynthesis_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    [Fintype G.edgeSet]
    [FiniteDimensional F2 (G.edgeSet → Color)]
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (∃ C : G.EdgeColoring Color,
        IsTaitEdgeColoring G C ∧ Theorem49BoundaryRootSynthesis emb C) ∧
          Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G}
        (C : G.EdgeColoring Color),
        IsTaitEdgeColoring G C →
          Theorem49BoundaryRootSynthesis emb C →
            Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb =>
        ∃ C : G.EdgeColoring Color,
          IsTaitEdgeColoring G C ∧ Theorem49BoundaryRootSynthesis emb C)
      hWitness ?_
  intro emb hP
  rcases hP with ⟨C, hC, hSynthesis⟩
  exact h C hC hSynthesis

/-- Route-facing special case of the generic failed converse: an honest closed-walk annulus
source can coexist with a forcing interior edge on some embedding, so there is no universal
same-embedding derivation from that source shell to annulus-root adjacency-distance data. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb => Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
      hWitness

/-- The same forcing-edge witness blocks any universal same-embedding derivation from annulus
boundary reachability plus cyclic ordered face-arc data to annulus-root adjacency-distance
data. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb)) ∧
          Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) →
            Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb =>
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb))
      hWitness ?_
  intro emb hP
  exact h hP.1 hP.2

/-- The same forcing-edge witness also blocks the weaker same-embedding derivation from annulus
boundary reachability plus bundled selected-boundary arc geometry to annulus-root
adjacency-distance data. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb)) ∧
          Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) →
            Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb =>
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb))
      hWitness ?_
  intro emb hP
  exact h hP.1 hP.2

/-- The same witness rules out any annulus construction whose peeled faces are required to be
edge-disjoint from selected-boundary support. -/
theorem false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstruction emb)
    (hpeelInterior : ∀ f ∈ data.peelFaces,
      Disjoint (emb.faceBoundary f.1)
        (selectedBoundarySupport emb.faceBoundary emb.faces emb.faces))
    (hw : ForcingInteriorEdgeWitness emb) :
    False := by
  exact
    Mettapedia.GraphTheory.FourColor.Theorem49InteriorVerticesEndpointObstruction.false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior_of_forcing_interiorEdge
      data hpeelInterior hw.heInterior hw.hforcing

theorem not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hw : ForcingInteriorEdgeWitness emb) :
    ¬ Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  rintro ⟨data⟩
  rcases data.construction
      |>.exists_peelFace_witnessEdge_eq_and_faceBoundary_disjoint_selectedBoundarySupport_of_mem_interiorEdgeSupport
        data.hpeelInterior hw.heInterior with
    ⟨_f, _hfPeel, _hfe, heFace, hdisjoint⟩
  rcases hw.hforcing heFace with ⟨b, hbFace, hbSelected⟩
  exact (Finset.disjoint_left.mp hdisjoint) hbFace hbSelected

theorem
    everyInteriorEdgeHasBoundaryFreeIncidentFace_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace emb := by
  intro e heInterior
  rcases data.construction
      |>.exists_peelFace_witnessEdge_eq_and_faceBoundary_disjoint_selectedBoundarySupport_of_mem_interiorEdgeSupport
        data.hpeelInterior heInterior with
    ⟨f, _hfPeel, _hfe, heFace, hdisjoint⟩
  exact ⟨f, heFace, hdisjoint⟩

noncomputable def
    boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) :
    BoundaryFreeIncidentFaceSelector emb :=
  boundaryFreeIncidentFaceSelector_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
    (everyInteriorEdgeHasBoundaryFreeIncidentFace_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
      data)

theorem not_nonempty_forcingInteriorEdgeWitness_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) :
    ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_nonempty_forcingInteriorEdgeWitness_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
      (everyInteriorEdgeHasBoundaryFreeIncidentFace_of_planarBoundaryAnnulusConstructionBoundarySupportFaceData
        data)

theorem
    everyInteriorEdgeHasBoundaryFreeIncidentFace_of_planarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb) :
    EveryInteriorEdgeHasBoundaryFreeIncidentFace emb := by
  intro e heInterior
  rcases data.construction
      |>.exists_peelFace_witnessEdge_eq_and_faceBoundary_disjoint_selectedBoundarySupport_of_mem_interiorEdgeSupport
        data.hpeelInterior heInterior with
    ⟨f, _hfPeel, _hfe, heFace, hdisjoint⟩
  exact ⟨f, heFace, hdisjoint⟩

/-- The downstream face-layer construction shell already carries the local no-forcing witness
needed by every selector/construction continuation: for each interior edge it chooses an incident
peeled face whose whole boundary avoids selected-boundary support. -/
noncomputable def
    boundaryFreeIncidentFaceSelector_of_planarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb) :
    BoundaryFreeIncidentFaceSelector emb :=
  boundaryFreeIncidentFaceSelector_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
    (everyInteriorEdgeHasBoundaryFreeIncidentFace_of_planarBoundaryAnnulusConstructionFaceLayerData
      data)

theorem not_nonempty_forcingInteriorEdgeWitness_of_planarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (data : PlanarBoundaryAnnulusConstructionFaceLayerData emb) :
    ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  exact
    not_nonempty_forcingInteriorEdgeWitness_of_everyInteriorEdgeHasBoundaryFreeIncidentFace
      (everyInteriorEdgeHasBoundaryFreeIncidentFace_of_planarBoundaryAnnulusConstructionFaceLayerData
        data)

theorem not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hw : ForcingInteriorEdgeWitness emb) :
    ¬ Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  rintro ⟨data⟩
  exact false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior
    data.construction data.hpeelInterior hw

theorem not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hw : ForcingInteriorEdgeWitness emb) :
    ¬ Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  rintro ⟨data⟩
  exact false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior
    data.construction data.hpeelInterior hw

theorem not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hw : ForcingInteriorEdgeWitness emb) :
    ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  rintro ⟨data⟩
  exact false_of_planarBoundaryAnnulusConstruction_and_hpeelInterior
    data.construction data.hpeelInterior hw

/-- The same forcing-edge witness blocks any universal same-embedding derivation from `P` to
the weakest construction-side shell whose peeled faces must avoid selected-boundary support. -/
theorem not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V} (P : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      P emb ∧ Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        P emb → Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  intro h
  rcases hWitness with ⟨emb, hP, ⟨hw⟩⟩
  exact not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData (emb := emb) hw
    (h (emb := emb) hP)

/-- Route-facing construction-shell special case: an honest closed-walk annulus source can
coexist with a forcing interior edge on some embedding, so that source shell alone cannot
universally yield the boundary-support face data needed by the construction-side route. -/
theorem not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb => Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
      hWitness

/-- The same forcing-edge witness blocks any universal same-embedding derivation from `P` to
the intermediate face-partition construction shell. -/
theorem not_forall_nonempty_planarBoundaryAnnulusConstructionFacePartitionData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V} (P : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      P emb ∧ Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        P emb → Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  intro h
  rcases hWitness with ⟨emb, hP, ⟨hw⟩⟩
  exact not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData (emb := emb) hw
    (h (emb := emb) hP)

/-- The same forcing-edge witness blocks any universal same-embedding derivation from `P` to
the intermediate positive-frontier construction shell. -/
theorem not_forall_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V} (P : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      P emb ∧ Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        P emb → Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  intro h
  rcases hWitness with ⟨emb, hP, ⟨hw⟩⟩
  exact not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData (emb := emb) hw
    (h (emb := emb) hP)

/-- The same forcing-edge witness blocks any universal same-embedding derivation from `P` to
the downstream construction face-layer package used to lower into annulus decomposition. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V} (P : PlaneEmbeddingWithBoundary G → Prop)
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      P emb ∧ Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        P emb → Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  rcases hWitness with ⟨emb, hP, ⟨hw⟩⟩
  exact not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData (emb := emb) hw
    (h (emb := emb) hP)

/-- Route-facing face-layer special case: an honest closed-walk annulus source can coexist with a
forcing interior edge on some embedding, so that source shell alone cannot universally yield the
construction face-layer data used later in the annulus-decomposition route. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
        Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) →
          Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb => Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
      hWitness

/-- The same forcing-edge witness also refutes a universal face-layer theorem on the stronger
reachability-plus-cyclic-ordered-face-arc source shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb)) ∧
          Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) →
            Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb =>
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb))
      hWitness ?_
  intro emb hP
  exact h hP.1 hP.2

/-- The same forcing-edge witness likewise refutes a universal face-layer theorem on the weaker
reachability-plus-selected-boundary-arc source shell. -/
theorem
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      (Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
        Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb)) ∧
          Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) →
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) →
            Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  intro h
  refine
    not_forall_nonempty_planarBoundaryAnnulusConstructionFaceLayerData_of_exists_embedding_with_property_and_forcingInteriorEdgeWitness
      (P := fun emb =>
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb))
      hWitness ?_
  intro emb hP
  exact h hP.1 hP.2

/-- Route-facing summary: an honest closed-walk annulus boundary source plus a forcing interior
edge still does not yield the peeled interior-dual package. -/
theorem
    closedWalkAnnulusBoundarySource_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) :=
  ⟨hsource, not_nonempty_interiorDualBoundaryRootAdjDistancePeelData hw⟩

/-- The same forcing-edge witness also blocks the current two-sided annulus-root route data
itself, so no boundary-split repackaging can rescue the source shell on that embedding. -/
theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) :=
  ⟨hsource, not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData hw⟩

/-- The same forcing-edge witness also blocks the current two-sided annulus-root parent route
data itself, so no parent-oriented repackaging can rescue the source shell on that embedding. -/
theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) :=
  ⟨hsource, not_nonempty_planarBoundaryAnnulusRootParentPeelData hw⟩

/-- Even after adjoining the stronger cyclic ordered face-arc shell already induced by the
honest closed-walk source, the same forcing interior edge still blocks the current two-sided
annulus-root route data. -/
theorem
    closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    ⟨hsource,
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_of_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource
        hsource,
      not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData hw⟩

/-- Even after adjoining the stronger cyclic ordered face-arc shell already induced by the
honest closed-walk source, the same forcing interior edge still blocks the current two-sided
annulus-root parent route data. -/
theorem
    closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    ⟨hsource,
      nonempty_planarBoundaryCyclicOrderedFaceArcEmbeddingData_of_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource
        hsource,
      not_nonempty_planarBoundaryAnnulusRootParentPeelData hw⟩

/-- The same remains true after weakening the extra boundary-order data to the bundled
selected-boundary-arc shell extracted from the honest source. -/
theorem
    closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact
    ⟨hsource,
      nonempty_planarBoundarySelectedBoundaryArcGeometry_of_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource
        hsource,
      not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData hw⟩

/-- The same remains true after weakening the extra boundary-order data to the bundled
selected-boundary-arc shell extracted from the honest source. -/
theorem
    closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact
    ⟨hsource,
      nonempty_planarBoundarySelectedBoundaryArcGeometry_of_nonempty_planarBoundaryClosedWalkAnnulusBoundarySource
        hsource,
      not_nonempty_planarBoundaryAnnulusRootParentPeelData hw⟩

/-- The same forcing-edge witness also blocks the weakest current annulus-construction shell. -/
theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) :=
  ⟨hsource, not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData hw⟩

/-- The same forcing-edge witness also blocks the intermediate face-partition construction shell.
-/
theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionFacePartitionData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) :=
  ⟨hsource, not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData hw⟩

/-- The same forcing-edge witness also blocks the reduced positive-frontier construction shell. -/
theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) :=
  ⟨hsource, not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData hw⟩

/-- The same forcing-edge witness also blocks the concrete face-layer shell that feeds the
annulus decomposition route. -/
theorem
    closedWalkAnnulusBoundarySource_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hsource : Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) :=
  ⟨hsource, not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData hw⟩

/-- Even after adjoining annulus root reachability and cyclic ordered face-arc data, the same
forcing interior edge still blocks the peeled interior-dual package. -/
theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (hcyclic : Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  exact ⟨hreach, hcyclic, not_nonempty_interiorDualBoundaryRootAdjDistancePeelData hw⟩

/-- The same source-side strengthening still does not reach the current two-sided annulus-root
route data when a forcing interior edge is present. -/
theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (hcyclic : Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact ⟨hreach, hcyclic, not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData hw⟩

/-- The same source-side strengthening still does not reach the current two-sided annulus-root
parent route data when a forcing interior edge is present. -/
theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (hcyclic : Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact ⟨hreach, hcyclic, not_nonempty_planarBoundaryAnnulusRootParentPeelData hw⟩

/-- The same source-side strengthening still does not reach the weakest current construction-side
shell when a forcing interior edge is present. -/
theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (hcyclic : Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  exact
    ⟨hreach, hcyclic,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData hw⟩

/-- The same source-side strengthening still does not reach the intermediate face-partition shell
when a forcing interior edge is present. -/
theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionFacePartitionData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (hcyclic : Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  exact
    ⟨hreach, hcyclic,
      not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData hw⟩

/-- The same source-side strengthening still does not reach the reduced positive-frontier shell
when a forcing interior edge is present. -/
theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (hcyclic : Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  exact
    ⟨hreach, hcyclic,
      not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData hw⟩

/-- The same source-side strengthening still does not reach the concrete face-layer shell used
to lower into annulus decomposition when a forcing interior edge is present. -/
theorem
    annulusBoundaryReachability_and_cyclicOrderedFaceArcEmbeddingData_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (hcyclic : Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    ⟨hreach, hcyclic,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData hw⟩

/-- Weakening the cyclic source shell to bundled selected-boundary arc geometry still does not
reach the peeled interior-dual package when the same embedding carries a forcing interior edge. -/
theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (harc : Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
      ¬ Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  exact ⟨hreach, harc, not_nonempty_interiorDualBoundaryRootAdjDistancePeelData hw⟩

/-- The same weakening to bundled selected-boundary arc geometry still does not reach the
current two-sided annulus-root route data when a forcing interior edge is present. -/
theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (harc : Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  exact ⟨hreach, harc, not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData hw⟩

/-- The same weakening to bundled selected-boundary arc geometry still does not reach the
current two-sided annulus-root parent route data when a forcing interior edge is present. -/
theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (harc : Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  exact ⟨hreach, harc, not_nonempty_planarBoundaryAnnulusRootParentPeelData hw⟩

/-- The same weakening to bundled selected-boundary arc geometry still does not reach even the
weakest current construction-side shell when a forcing interior edge is present. -/
theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionBoundarySupportFaceData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (harc : Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionBoundarySupportFaceData emb) := by
  exact
    ⟨hreach, harc,
      not_nonempty_planarBoundaryAnnulusConstructionBoundarySupportFaceData hw⟩

/-- The same weakening to bundled selected-boundary arc geometry still does not reach the
intermediate face-partition shell when a forcing interior edge is present. -/
theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionFacePartitionData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (harc : Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  exact
    ⟨hreach, harc,
      not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData hw⟩

/-- The same weakening to bundled selected-boundary arc geometry still does not reach the
reduced positive-frontier shell when a forcing interior edge is present. -/
theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionPositiveFrontierData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (harc : Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  exact
    ⟨hreach, harc,
      not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData hw⟩

/-- The same weakening to bundled selected-boundary arc geometry still does not reach the
concrete face-layer shell used to lower into annulus decomposition when a forcing interior edge
is present. -/
theorem
    annulusBoundaryReachability_and_selectedBoundaryArcGeometry_does_not_imply_planarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} {emb : PlaneEmbeddingWithBoundary G}
    (hreach : Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb))
    (harc : Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb))
    (hw : ForcingInteriorEdgeWitness emb) :
    Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
      Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
      ¬ Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  exact
    ⟨hreach, harc,
      not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData hw⟩

/-- Graph-level existential form of the forcing-edge obstruction at the honest source surface:
no single embedding can simultaneously carry the closed-walk annulus source, a forcing interior
edge witness, and the peeled interior-dual boundary-root adjacency-distance package. -/
theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_interiorDualBoundaryRootAdjDistancePeelData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (InteriorDualBoundaryRootAdjDistancePeelData emb.faces emb.faceBoundary) := by
  rintro ⟨emb, _hsource, ⟨hw⟩, hdata⟩
  exact not_nonempty_interiorDualBoundaryRootAdjDistancePeelData (emb := emb) hw hdata

/-- Graph-level existential form on the current two-sided annulus-root lane: no single embedding
can simultaneously carry the honest closed-walk annulus source, a forcing interior edge witness,
and the annulus-root adjacency-distance package. -/
theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  rintro ⟨emb, _hsource, ⟨hw⟩, hdata⟩
  exact not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData (emb := emb) hw hdata

/-- Graph-level existential form on the current two-sided annulus-root parent lane: no single
embedding can simultaneously carry the honest closed-walk annulus source, a forcing interior
edge witness, and the annulus-root parent package. -/
theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  rintro ⟨emb, _hsource, ⟨hw⟩, hdata⟩
  exact not_nonempty_planarBoundaryAnnulusRootParentPeelData (emb := emb) hw hdata

/-- Even after adjoining the stronger cyclic ordered face-arc shell already induced by the
honest closed-walk source, no single embedding can carry that strengthened source package,
a forcing interior-edge witness, and the current two-sided annulus-root route data. -/
theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  rintro ⟨emb, _hsource, _hcyclic, ⟨hw⟩, hdata⟩
  exact not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData (emb := emb) hw hdata

/-- Even after adjoining the stronger cyclic ordered face-arc shell already induced by the
honest closed-walk source, no single embedding can carry that strengthened source package,
a forcing interior-edge witness, and the current two-sided annulus-root parent route data. -/
theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  rintro ⟨emb, _hsource, _hcyclic, ⟨hw⟩, hdata⟩
  exact not_nonempty_planarBoundaryAnnulusRootParentPeelData (emb := emb) hw hdata

/-- The same remains true after weakening the extra boundary-order data on top of the honest
source shell to the bundled selected-boundary-arc geometry. -/
theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  rintro ⟨emb, _hsource, _harc, ⟨hw⟩, hdata⟩
  exact not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData (emb := emb) hw hdata

/-- The same remains true after weakening the extra boundary-order data on top of the honest
source shell to the bundled selected-boundary-arc geometry. -/
theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  rintro ⟨emb, _hsource, _harc, ⟨hw⟩, hdata⟩
  exact not_nonempty_planarBoundaryAnnulusRootParentPeelData (emb := emb) hw hdata

/-- Graph-level existential form at the stronger cyclic ordered face-arc source surface:
no single embedding can carry annulus reachability, cyclic ordered face arcs, a forcing
interior edge witness, and the intermediate face-partition shell. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFacePartitionData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  rintro ⟨emb, _hreach, _hcyclic, ⟨hw⟩, hpart⟩
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData (emb := emb) hw hpart

/-- Graph-level existential form at the stronger cyclic ordered face-arc source surface:
no single embedding can carry annulus reachability, cyclic ordered face arcs, a forcing
interior edge witness, and the reduced positive-frontier shell. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionPositiveFrontierData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  rintro ⟨emb, _hreach, _hcyclic, ⟨hw⟩, hfrontier⟩
  exact
    not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData (emb := emb) hw hfrontier

/-- Graph-level existential form at the stronger cyclic ordered face-arc source surface on the
current two-sided annulus-root lane. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  rintro ⟨emb, _hreach, _hcyclic, ⟨hw⟩, hdata⟩
  exact
    not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData (emb := emb) hw hdata

/-- Graph-level existential form at the stronger cyclic ordered face-arc source surface on the
current two-sided annulus-root parent lane. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  rintro ⟨emb, _hreach, _hcyclic, ⟨hw⟩, hdata⟩
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData (emb := emb) hw hdata

/-- Graph-level existential form at the weaker selected-boundary-arc source surface:
no single embedding can carry annulus reachability, bundled selected-boundary arc geometry,
a forcing interior edge witness, and the intermediate face-partition shell. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFacePartitionData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionFacePartitionData emb) := by
  rintro ⟨emb, _hreach, _harc, ⟨hw⟩, hpart⟩
  exact
    not_nonempty_planarBoundaryAnnulusConstructionFacePartitionData (emb := emb) hw hpart

/-- Graph-level existential form at the weaker selected-boundary-arc source surface:
no single embedding can carry annulus reachability, bundled selected-boundary arc geometry,
a forcing interior edge witness, and the reduced positive-frontier shell. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionPositiveFrontierData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionPositiveFrontierData emb) := by
  rintro ⟨emb, _hreach, _harc, ⟨hw⟩, hfrontier⟩
  exact
    not_nonempty_planarBoundaryAnnulusConstructionPositiveFrontierData (emb := emb) hw hfrontier

/-- Graph-level existential form at the weaker selected-boundary-arc source surface on the
current two-sided annulus-root lane. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootAdjDistancePeelData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootAdjDistancePeelData emb) := by
  rintro ⟨emb, _hreach, _harc, ⟨hw⟩, hdata⟩
  exact
    not_nonempty_planarBoundaryAnnulusRootAdjDistancePeelData (emb := emb) hw hdata

/-- Graph-level existential form at the weaker selected-boundary-arc source surface on the
current two-sided annulus-root parent lane. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusRootParentPeelData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusRootParentPeelData emb) := by
  rintro ⟨emb, _hreach, _harc, ⟨hw⟩, hdata⟩
  exact
    not_nonempty_planarBoundaryAnnulusRootParentPeelData (emb := emb) hw hdata

/-- Graph-level existential form at the honest source surface for the concrete face-layer shell:
no single embedding can simultaneously carry the closed-walk annulus source, a forcing interior
edge witness, and the annulus-construction face-layer data used to lower into decomposition. -/
theorem
    not_exists_embedding_closedWalkAnnulusBoundarySource_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryClosedWalkAnnulusBoundarySource emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  rintro ⟨emb, _hsource, ⟨hw⟩, hlayer⟩
  exact not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData (emb := emb) hw hlayer

/-- Graph-level existential form at the stronger cyclic ordered face-arc source surface for the
concrete face-layer shell. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_cyclicOrderedFaceArcEmbeddingData_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundaryCyclicOrderedFaceArcEmbeddingData emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  rintro ⟨emb, _hreach, _hcyclic, ⟨hw⟩, hlayer⟩
  exact not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData (emb := emb) hw hlayer

/-- Graph-level existential form at the weaker selected-boundary-arc source surface for the
concrete face-layer shell. -/
theorem
    not_exists_embedding_annulusBoundaryReachabilityData_and_selectedBoundaryArcGeometry_and_forcingInteriorEdgeWitness_and_planarBoundaryAnnulusConstructionFaceLayerData
    {G : SimpleGraph V} :
    ¬ ∃ emb : PlaneEmbeddingWithBoundary G,
        Nonempty (PlanarBoundaryAnnulusBoundaryReachabilityData emb) ∧
          Nonempty (PlanarBoundarySelectedBoundaryArcGeometry emb) ∧
          Nonempty (ForcingInteriorEdgeWitness emb) ∧
          Nonempty (PlanarBoundaryAnnulusConstructionFaceLayerData emb) := by
  rintro ⟨emb, _hreach, _harc, ⟨hw⟩, hlayer⟩
  exact not_nonempty_planarBoundaryAnnulusConstructionFaceLayerData (emb := emb) hw hlayer

/-- A same-embedding model with boundary reachability, honest closed walks, the
at-most-one-interior-edge-per-face condition, and a forcing interior edge refutes the universal
claim that those three source-side hypotheses exclude forcing interior edges. -/
theorem
    not_forall_not_nonempty_forcingInteriorEdgeWitness_of_exists_embedding_reachability_and_closedWalkEmbedding_and_atMostOneInteriorEdge_and_forcingInteriorEdgeWitness
    {G : SimpleGraph V}
    (hWitness : ∃ emb : PlaneEmbeddingWithBoundary G,
      ∃ _ : PlanarBoundaryAnnulusBoundaryReachabilityData emb,
        ∃ _ : PlanarBoundaryClosedWalkEmbeddingData emb,
          (∀ f : AmbientFace emb.faces,
            ((emb.faceBoundary f.1).filter
                (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) ∧
            Nonempty (ForcingInteriorEdgeWitness emb)) :
    ¬ ∀ {emb : PlaneEmbeddingWithBoundary G},
        PlanarBoundaryAnnulusBoundaryReachabilityData emb →
          PlanarBoundaryClosedWalkEmbeddingData emb →
            (∀ f : AmbientFace emb.faces,
              ((emb.faceBoundary f.1).filter
                  (· ∈ interiorEdgeSupport emb.faceBoundary emb.faces)).card ≤ 1) →
              ¬ Nonempty (ForcingInteriorEdgeWitness emb) := by
  intro h
  rcases hWitness with ⟨emb, hreach, hwalk, hatMostOne, hforce⟩
  exact h hreach hwalk hatMostOne hforce

end Theorem49ForcingInteriorEdgeObstruction

end Mettapedia.GraphTheory.FourColor
